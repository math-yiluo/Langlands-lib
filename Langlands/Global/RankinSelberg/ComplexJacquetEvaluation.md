# Linear evaluation of the entire complex Jacquet family

The fixed-profile Jacquet family is determined by its entire dependence on the exponents at each group argument and its agreement with the exact open-cell integral on the strict chamber. The module chooses this family and proves uniqueness using the affine-line identity theorem.

The map `transferProfile` changes the inducing exponents of a compact-finite standard vector while retaining its restriction to the unitary group. Compose it with the chamber intertwiner to obtain a linear chamber evaluation for vectors at any reference parameter. The additivity and scalar identities of this evaluation extend by the same identity theorem. This gives `continuedJacquetFamilies` and its parameter evaluation `continuedJacquet` as linear maps on the actual standard modules.

The left Whittaker law extends from the exact chamber formula. Right unitary translation commutes with transfer of the compact profile, and the defining chamber integral commutes with it by associativity of the group multiplication. Continuing this identity gives right unitary equivariance at all parameters. At the input parameter, transfer of the compact profile recovers the original standard vector. This identifies the evaluation with the original integral on the strict chamber.
