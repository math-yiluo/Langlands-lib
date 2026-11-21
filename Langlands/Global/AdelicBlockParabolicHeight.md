# Polynomial height control for the actual block parabolic

`blockProductHeight` multiplies the dimension-scaled adelic heights of the Levi blocks. The matrix and inverse entries of each projected block come from the corresponding entries of the parabolic matrix and its inverse. Comparing local maxima and taking the products over places bounds the Levi height by a power of the ambient height.

The actual determinant character is a scheme character on the block general linear group. Closed-embedding height domination bounds its normalized determinant norm and its reciprocal. Pointwise finite products and positive powers preserve polynomial growth. The formula for the adelic block modulus and the inequality \(\sqrt{x}\le\max(1,x)\) give the bound for its positive half.

This derived comparison is used for moderate growth of the inducing sections in Langlands, *On the notion of an automorphic representation* (1979), proof of Proposition 2, printed pp. 204–206, Corvallis Part I PDF pp. 199–201. The normalized block determinants here are the actual ones in `AdelicBlockDeterminantCharacter`.
