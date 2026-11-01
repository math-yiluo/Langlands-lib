# Full support of integral ideals and exact-dimensional coherent cuts

`integralSupportDimension` proves the three clauses of
`IntegralSupportDimensionStatement` for schemes in arbitrary universe `u`.

For a nonzero ideal monomorphism on an integral scheme,
`exists_nonempty_open_isIso_ideal` supplies a nonempty open on which the ideal
inclusion is invertible. Compose that isomorphism with the restriction-unit
isomorphism. The published dense-open support criterion gives full closed
stalk support. The homeomorphism from the universal-set subtype to the scheme
then identifies their topological Krull dimensions.

For a generically generating section of a line bundle on an integral scheme,
the actual abelian-stalk support of its categorical cokernel is the complement
of the entire generation open. This complement is closed, so taking closure
does not change it. Unfolding `supportDimension` gives the second clause.
The helper `coe_closedStalkSupport_sectionHom_cokernel` retains the set equality.

For an ample line bundle on an integral locally Noetherian scheme of dimension
`d + 1`, the exact-dimensional section theorem supplies a positive tensor-power
section with nonempty generation open and vanishing-set dimension plus one
equal to `d + 1`. The actual tensor power is locally free of rank one and hence
quasi-coherent with finite affine sections. Closure under categorical cokernels
gives both properties for the section cokernel. Its support dimension is the
vanishing-set dimension by the previous clause. The discrete finite-dimension
order on `WithBot ℕ∞` then makes that dimension exactly `d`, including `d = 0`.

This is an internal combination of the ideal-open, actual section-support,
exact ample-cut and coherent-closure results. It does not assert an Euler
polynomial or leading-coefficient positivity theorem.
