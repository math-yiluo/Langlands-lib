# Schur's lemma and irreducible subspaces of Hilbert sums

`Langlands.TraceFormula.unitarySchurHilbertSum` proves
`Langlands.TraceFormula.UnitarySchurHilbertSumStatement` with independent universe
parameters for the Hilbert space and the group.

## Scalar commutant

Mathlib's `LinearMap.norm_map_iff_inner_map_map` turns norm preservation into
inner-product preservation. On a nonzero space, the closed invariant subspace
condition gives `Langlands.Archimedean.IsTopologicallyIrreducible`, so
`Langlands.Archimedean.exists_eq_scalar_of_unitary_commute` gives the scalar
commutant. That result uses continuous functional calculus on the self-adjoint
parts of a commuting operator. Two distinct spectral points would give
commuting operators with zero product and hence a proper nonzero closed
invariant kernel. In the zero space, every endomorphism is zero.
[Scalar commutant proof](../Representation/Archimedean/UnitaryCommutant.md)

This proves the implication from irreducibility to the scalar commutant in
Folland's Theorem 3.5(a). Folland uses spectral projections for the self-adjoint
step. For the Lean statement the argument uses only the group law and
unitarity, so it applies to abstract groups.

## Equivalence to a summand

For a nonzero vector of the irreducible closed invariant subspace `Q`, some
orthogonal projection onto a summand is nonzero. To see this, use
`IsHilbertSum.linearIsometryEquiv` and test the inner product with a vector in a
single coordinate. Mathlib's `lp.inner_single_left` computes this inner product
in the external sum. In the ambient space it is computed by the orthogonal
projection, the adjoint of the summand inclusion by `Submodule.adjoint_subtypeL`.
If every projection vanished, testing each coordinate against itself would force
the vector to vanish.

`IsotypicTrace.restrictAction` gives the actions on `Q` and the selected summand
`P`. The summand inclusion intertwines, so its adjoint intertwines in reverse
by `Langlands.Archimedean.adjoint_mem_boundedIntertwiners`. This proves the
projection equivariance of Folland's Propositions 3.1 and 3.4 in the form of an
intertwiner into `P`. Composing the projection with the inclusion of `Q` gives a
nonzero intertwiner `T : Q →L[ℂ] P`. Its adjoint intertwines in reverse by the
same theorem. [Restricted actions](IsotypicTrace/RestrictAction.md)
[Adjoints of bounded intertwiners](../Representation/Archimedean/HilbertIntertwinerEvaluation.md)

By `IsotypicTrace.restrictAction_irreducible`, the actions on the subtypes
satisfy the closed invariant subspace criterion. The scalar commutant on `Q`
gives `T† T = c • id`. Using `ContinuousLinearMap.norm_adjoint_comp_self` and the
norm of the identity on nonzero `Q` gives `‖c‖ = ‖T‖²`. Taking norms in the
inner-product identity for `T† T` gives `‖T x‖ = ‖T‖ ‖x‖` for every `x : Q`.
Thus `‖T‖⁻¹ • T` is a linear isometric intertwiner. Its range is closed by
completeness of `Q`, invariant by equivariance, and nonzero by injectivity.
Irreducibility of `P` makes the range all of `P`, so
`LinearIsometryEquiv.ofSurjective` gives the asserted equivalence. This applies
the normalization in Folland's Theorem 3.5(b) using the scalar Gram operator on
`Q` and the range criterion on `P`.

## Source

Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, second edition,
CRC Press, 2015, §3.1, Propositions 3.1 and 3.4 and Theorem 3.5(a,b), printed
pp. 76–77 (PDF pp. 89–90). The retained source is
`folland-2015-abstract-harmonic-analysis-second` with SHA-256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
