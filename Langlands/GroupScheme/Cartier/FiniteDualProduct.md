# The alternating pairing on a product with its finite dual

`productWithDual` is the actual product of a finite locally free commutative group scheme \(G\) over an affine base with its finite dual spectrum. Its point group over a test scheme consists of a point of \(G\) and a point of the dual. For two such pairs \((x,\chi)\) and \((y,\psi)\), `productWithDualPairing` gives \(\psi(x)\chi(y)^{-1}\) in the point group of the multiplicative group. It is multiplicative in both arguments, alternating, and natural under restriction to any test scheme.

`productWithDualMap` takes two actual maps on the factors and gives their product map. The Lean proofs verify the coordinate rule, identity, and composition. If \(f:G\to H\) and \(g:H\to G\) are actual maps, then \(f\times g^\vee\) and \(g\times f^\vee\) are adjoint for the two alternating pairings. The proof applies the adjointness of finite dual evaluation to each factor. This equality supplies the compatibility needed when the two maps are the inclusion and multiplication transition of scalar torsion.

This is the finite-level product and alternating evaluation used for the tautological polarization of the split object in Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321). The evaluation construction is from Demazure and Gabriel (1970), Chapter II, §1, no. 2, 2.10, printed pp. 156–158 (PDF pp. 186–188).
