import Data.List

convertBinToDec x = convertBinToDecH (x) (0)
convertBinToDecH x y 
	|x > 0 = (x `mod` 10)*2^y + convertBinToDecH(x `div` 10)(y+1)
	|otherwise = 0
	
replaceIthItem v (x:xs) i 
                           | i>0 =  (x:replaceIthItem v xs (i-1))
						   | i==0 =   v:xs
logBase2 x = logBase 2 x 

fillzeros x num 
                 |num > 0 = fillzeros (['0'] ++ x) (num-1)
                 | num == 0 = x				

splitEvery num list = splithepler num (splitAt num list)
 
splithepler num (x,[]) = [x]
splithepler num (x,xs) = [x] ++ splithepler num (splitAt num xs)

getNumBits  x "fullyAssoc" cache = 0 
getNumBits  x "directMap" cache = logBase2 x
getNumBits  x "setAssoc" cache = logBase2 x
                       					  
                           				  
                 


convert  x= read x :: Int  

tostring x = show x


getntho (x:xs) pos = (x:xs)!!pos 



getelementidx e l = getelementidxH e l 0
getelementidxH e (x:xs) idx
	| e==x = idx
	| otherwise = getelementidxH e xs (idx+1)

getelementidxH e [] idx = -1

------------------------------------------------GetDataFromCache------------------------------------------------------
data Output a = Out (a, Int) | NoOutput deriving (Show, Eq)
data Item a = It Tag (Data a) Bool Int | NotPresent deriving (Show, Eq)
data Tag = T Int deriving (Show, Eq)
data Data a = D a deriving (Show, Eq)



--getDataFromCache :: (Integral b, Eq a) => [Char] -> [Item a] -> [Char] -> b -> Output a
getDataFromCache address list  "directMap" numbits = getDatadir  list (convertAddress (convert address) numbits "directMap" ) 
getDataFromCache tag cache "fullyAssoc" 0 = getDataFromCacheH (convert tag) cache 0
getDataFromCache string cache "setAssoc" bitsNum = getDataFromCacheH2 tag (convertBinToDec idx) cache bitsNum where (tag,idx) = (convertAddress (convert string) bitsNum "setAssoc")



------------------------------------------------GetDataFromCacheHelperFunctions------------------------------------------------------
getDataFromCacheH _ [] _ = NoOutput
getDataFromCacheH tag ((It(T t) (D d) valid _):xs) hops
	|valid == True && tag == t = Out(d,hops)
	|otherwise = getDataFromCacheH tag xs (hops+1)
	
	


getDataFromCacheH2 tag idx cache bitsNum = getDataFromCache (show tag) (getntho (splitEvery (2^bitsNum) cache) idx) "fullyAssoc" 0



------------------------------------------------directMap Helper Functions------------------------------------------------------

getDatadir (x:xs) (tag,idx)= check tag (getntho (x:xs) (convertBinToDec idx))

check  tag ((It(T t) (D d) valid _))                                 
								    | valid == True && tag == t  = Out(d,0)
								    | otherwise = NoOutput

 
extendtag tag num =  extendhelper (show tag) (6-num)
extendhelper tag num 
                      |(length tag) == num = tag
                      |otherwise = fillzeros tag (num -(length tag) )					  
 
extendidx idx num =  extendidxh (show idx) num
extendidxh idx num 
                      |(length idx) == num = idx
                      |otherwise = fillzeros idx (num -(length idx) )					  
  
 
getaddress tag idx num =  address(extendtag tag num , extendidx idx num )

address (tag,idx) = convertBinToDec(convert(tag ++ idx))

------------------------------------------------Convert Address------------------------------------------------------

convertAddress x y "directMap" = (div x (10^y) ,mod x (10^y))

convertAddress x y "fullyAssoc" = (x,y)

convertAddress x y "setAssoc" = (div x (10^y) ,mod x (10^y))



------------------------------------------------Replace In Cache------------------------------------------------------


replaceInCache tag idx memory oldCache "fullyAssoc" bitsNum = replaceInCacheFH tag (getntho memory (convertBinToDec tag)) oldCache oldCache 0
replaceInCache tag idx memory oldCache "directMap"  x = replacedir (convertBinToDec idx) tag oldCache memory (getaddress tag idx x )
replaceInCache tag idx memory oldCache "setAssoc" bitsNum = (repAssocH tag idx memory,newCache) 
					where newCache = (repAssocH3 oldCache idx (repAssocH2 tag idx memory oldCache bitsNum) bitsNum)


------------------------------------------------Replace In Cache Helper Function------------------------------------------------------
replaceInCacheFH tag d2 ((It(T t) (D d) valid o):xs) oldCache2 count
	|valid == False = (d2,orderplus1  (replaceIthItem (It (T tag) (D d2) True (-1)) oldCache2 count))
	|otherwise = replaceInCacheFH tag d2 xs oldCache2 (count+1)
replaceInCacheFH tag d2 [] oldCache count = replaceInCacheFH2 tag d2 oldCache oldCache 0 NotPresent

replaceInCacheFH2 tag d2 ((It(T t) (D d) valid o):xs) oldCache2 maxO maxE
	|maxO<o = replaceInCacheFH2 tag d2 xs oldCache2 o (It(T t) (D d) valid o)
	|otherwise = replaceInCacheFH2 tag d2 xs oldCache2 maxO maxE
replaceInCacheFH2 tag d2 [] oldCache2 maxO maxE = (d2,orderplus2 (replaceIthItem (It(T tag) (D d2) True (-1)) oldCache2 (getelementidx maxE oldCache2)))


orderplus1  [] = []
orderplus1 ((It(T t) (D d) valid o):xs) 
	|valid == True = (It(T t) (D d) valid (o+1)):(orderplus1  xs)
	|otherwise = (It(T t) (D d) valid o):(orderplus1  xs)
orderplus2 ((It(T t) (D d) valid o):xs) = (It(T t) (D d) valid (o+1)):(orderplus2 xs)
orderplus2 [] = []


	
	

 
replacedir idx tag oldCache memory location = switch  idx  tag  oldCache (getntho memory location) 
switch  idx  tag oldCache d  = (d , replaceIthItem (It(T tag) (D d) True 0) oldCache idx)




                          									

                                   
----------------------------------------------replaceInCacheSetAssociativeHelper Functions--------------------------------------------------------                                 

--replaceInCache:: Integral b =>Int -> Int -> [a] -> [Item a] -> [Char] -> b -> (a, [Item a])


repAssocH tag idx memory = getntho memory (convertBinToDec (convert(show tag ++ show idx)))
repAssocH2 tag idx memory oldCache bitsNum = a where (_,a) = (replaceInCacheFH tag (repAssocH tag idx memory) (getntho (splitEvery (2^bitsNum) oldCache) idx) (getntho (splitEvery (2^bitsNum) oldCache) idx) 0)

repAssocH3 oldCache idx new bitsNum = concat(replaceIthItem new (splitEvery (2^bitsNum) oldCache) (convertBinToDec idx))




----------------------------------------------Implemented Functions--------------------------------------------------------   

--when i place the implemented functions they give syntax errors





																		
																							








