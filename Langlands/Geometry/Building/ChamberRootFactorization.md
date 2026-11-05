# Extracting one root factor from the chamber Iwahori product

Worker 1313 authors this internal construction for the chamber-simple factorization task. All universes and actual field, group, torus, centralizer and apartment data are inherited from `ParahoricBuildingData`.

`lastRootEnumeration` enumerates the indivisible relative roots positive on a cocharacter with a prescribed positive indivisible root last. Its existence proof enumerates the finite root set with that root removed and appends the selected root.

`exists_mul_of_chamberIwahoriConclusion` assumes the existing chamber Iwahori conclusion for a chamber, point and cocharacter. Let `a` be a positive indivisible relative root. Let `K` and `U` be subgroups of the actual ambient rational-point group. Assume the full central factor and the depth-zero filtration of every other indivisible relative root lie in `K`, and that each element of the selected `a`-filtration is a product from `K` and `U`. Then every element of the actual chamber parahoric is a product from `K` and `U`. The other-root hypothesis concerns indivisible indices, exactly as in the ordered chamber product, so it does not require absorbing the double of `a` separately.

The proof puts `a` last in the positive enumeration and uses the exact range of the existing ordered chamber product. V4 collapses each doubled-root block to the actual filtration. Every negative factor and every positive factor before the last lie in `K`. Splitting the final factor and associating the product gives the claimed factorization. The negative enumeration contains no `a` because its pairing with the cocharacter is negative. Injectivity of the positive enumeration excludes `a` from its prefix.

This is a derived algebraic step in KP's proof of Theorem 7.5.1, printed p.259 / PDF p.290, with the corrections of 1 November 2024, PDF p.35. The source uses the chamber Iwahori product to single out one affine-root factor. This module supplies only the extraction from the already stated ordered product. It does not prove that product, the geometric filtration inclusions for a reflected chamber, the special doubled-root split, or `ChamberSimpleFactorizationStatement`.
