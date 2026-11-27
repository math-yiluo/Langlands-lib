# Maximal-simple-type intertwining from the beta-extension twist

`MaximalSimpleTypeIntertwiningReductionStatement` assumes `BetaExtensionTwistStatement` at the field and stratum-space universes of `MaximalSimpleTypeIntertwiningStatement`, with its three representation-carrier universes specialized to zero. Simple type data exhibit the Heisenberg representation, beta extension and auxiliary representation on finite complex coordinate spaces. The carrier of the maximal simple type itself remains in an independent universe. The theorem `maximalSimpleTypeIntertwining_of_twist` proves the implication.

For kind (a), the restriction of the auxiliary representation to the relative unit subgroup is irreducible by surjectivity of the single-layer reduction. This gives irreducibility on the entire group and makes the beta-extension twist theorem applicable. That theorem gives irreducibility of the tensor product and expresses its intertwining as the double product of the group with the relative cuspidal intertwining set in the centralizer.

The relative period-one calculation makes the middle set the product of the field units and the relative unit subgroup. The field units normalize the group by `simpleStratumGroupProperties`, so the double product reduces to the field-unit translates of the group. A normalizing element whose inverse intertwines an irreducible representation gives an isomorphism of the conjugate pair by Schur's lemma. This yields the claimed normalization for every field unit. Kind (b) is the level-zero period-one calculation and requires no twist premise.

This implements the reduction underlying Bushnell–Kutzko (1993), (5.5.11), printed p. 185, its maximal-order specialization on p. 203, and the normalization on p. 200.

The source is Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
