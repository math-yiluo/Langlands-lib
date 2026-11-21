# Differential of the local Bruhat product

At the Bruhat point \(b p\), where \(b\) is upper triangular and \(p\) is the permutation matrix times the unipotent factor, `bruhatCellMatrixParam` varies the point by the factors \(1+U\) and \(1+R\). The coordinates \(U\) and \(R\) run over the upper triangular and lower inversion subspaces. The product is smooth over the real scalars. Its derivative at zero sends \((U,R)\) to \(b(U+R)p\).

A normal factor with value \(1\) and derivative \(L\) at zero adds \(Lbp\) to this derivative. The resulting derivative sends \((U,R,L)\) to \(b(b^{-1}Lb+U+R)p\). The conjugated direct sum from `BruhatMatrixCoordinates` and multiplication by the two fixed units give an invertible real continuous linear map.

This is the differential needed for the transverse coordinates used in the proof of Shalika's Proposition 2.10, printed p. 182. The entry subspaces and the choice of local matrix product are derived coordinates for the formal proof.
