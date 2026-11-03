# Integral dual pullback and rational action comparisons

This internal construction combines the existing actual dual-map composition
laws, rational dual pullback, and exact integral inverse-multiple data. It is
intended for the integral-order model comparison in the Harris CM problem.

For a homomorphism `f : A ⟶ B` and an integral dual-valued map
`lamB : B ⟶ Bᵛ`, `integralDualPullback` is an explicit abbreviation of the
published `integralDualPullbackHom` in
`Langlands.AbelianScheme.Tate.WeilIntegralPolarizationComparison`. Thus it is
the actual composite `f ≫ lamB ≫ fᵛ`. The rationalization comparison is a
wrapper of the published `rationalDualPullbackHom0_homToHom0`, with equality
reversed.

`rationalDualPullbackHom0_smul_map` states that replacing a rational map by
`q • f` multiplies its dual pullback by `q²`. This is a wrapper of the
published `rationalDualPullbackHom0_smul_hom`, rewriting `q * q` as `q²`.
The integral composite and these two comparisons are reused rather than
reconstructed here.

`integralInverseData_dualPullback_multiple` applies this to actual maps
`f : A ⟶ B` and `g : B ⟶ A` whose composites are the same nonzero integer
multiple `N` of the identities. For an integral `lamA : A ⟶ Aᵛ`, the map
`lamB = g ≫ lamA ≫ gᵛ` has the exact rational equation
`f^*(lamB) = N² • lamA`. Composition coherence identifies the left side with
pullback along `f ≫ g`; the integral identity identifies that map with
`N • id`; the square-scaling and identity formulas finish the proof. The
conclusion is precisely the existing `IsRationalDualPullbackMultiple`
predicate.

`IsInvolutionCompatible.rationalDualPullback` treats arbitrary rational
actions of a ring with involution. If `f` intertwines the whole actions,
pullback of a compatible dual-valued rational map remains compatible. The
proof dualizes the intertwining equation at `star b`, reverses composition,
and reassociates the original compatibility equation.

In the rational algebra-action category,
`RationalAlgebraAction.action_eq_conjugate` writes the source action as the
conjugate of the target action under an equivariant rational isomorphism.
`action_injective_of_iso` and `action_injective_iff` consequently preserve
and reflect injectivity of the full rational algebra map.

All dual representability, geometry, evaluation and tensor/Picard coherence
inputs are retained explicitly. These are algebraic identities of actual
integral maps and their rationalizations. This module does not prove that
the transported integral dual-valued map is a polarization, nor does it
prove dimension invariance or CM representability.
