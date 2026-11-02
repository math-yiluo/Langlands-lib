# Terminal quotients of the actual normalized complex

Internal construction by Worker 194, depending on the separately owned
normalization adapter of Worker 23.

The incoming boundary in degree zero is zero. In degree `k + 1` it is the
actual image of the signed differential from degree `k`. Equivariance of that
differential proves invariance of the image. `Terminal` is the quotient of the
actual normalized homogeneous carrier by this submodule;
`terminalRepresentation` is its descended action. The canonical
`terminalProjection` is surjective, has exactly this kernel and kills the
incoming differential. Smoothness descends along the quotient projection.
`terminalObject` bundles this actual quotient in the full smooth category.
These are intrinsic quotient constructions and need no exactness theorem.

`terminalDegree I = |ι| - |I|` counts removed roots. `sharpObject A I` retains
the terminal cokernel in that degree. This definition by itself does not
identify the abstract finite ordered index with a reductive group's simple
relative roots or impose a support condition on `A`.

`degreeEquiv` from the complex module is equivariant and intertwines the actual
signed maps. `boundary_equiv` uses this identity and surjectivity of the degree
equivalence to identify the image submodules in both directions.
`terminalLinearEquiv` is the induced quotient equivalence and `terminalEquiv`
proves its equivariance on quotient representatives.
`terminalEquiv_projection` records the canonical projection square.

No terminal vanishing, full-smooth exactness, support retention, finite length
or irreducibility is asserted here. In particular this terminal comparison is
the normalization comparison for the same subgroup family, and does not supply
the associated-Levi Jacquet comparison of the erratum.
