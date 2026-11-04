# Same-subgroup finite positive Cartan cover

`RationalPointFamily.rationalPositiveCartanCover` proves the complete internal `RationalPositiveCartanCoverStatement`.

The finite positive product cover in the supplied Renard comparison has the same dominant valuation image as the actual Cartan representatives. Double-coset classification by rational-character valuations therefore transfers coverage to this product set, retaining the original compact subgroup from `D` and `x`.

Each positive uniformizer power has nonnegative pairing with every positive root, hence with each simple root. The existing character norm formula and the residue cardinality inequality give its membership in the intrinsic `CAplus`. The representation of the actual centralizer supplies centralizer membership for each finite representative. Its commutation with the torus power puts the two factors in the order required by `FiniteCartanCovering`.

All steps use the actual rational-point maps. The finite set is the image of the supplied finite positive cover in the actual centralizer point subgroup. This internal proof constructs no geometric existence input and establishes neither cuspidal coefficient compactness nor the final Howe implication.
