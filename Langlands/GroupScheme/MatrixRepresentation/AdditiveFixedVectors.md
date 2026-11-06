# Fixed vectors of actual additive-group representations

Begin with an actual matrix representation `ρ` of the
one-dimensional vector group over a field `k`, with a finite decidable
coordinate type `n`. Define `polynomialOrbit ρ v` by multiplying the
universal univariate matrix by the constant vector `v`. Define
`fixedSubmodule ρ` as the intersection of the kernels of every
positive-degree coefficient operator.

Coefficient extraction commutes with the finite row sums and multiplication
by constant polynomials, so the degree `m` coefficient of the polynomial
orbit is `D_m v`. As `D_0=1`, membership in `fixedSubmodule` is equivalent
to the polynomial orbit being the constant vector `v`. Evaluation then
shows that every such vector remains fixed over every commutative test
algebra. Conversely, fixedness at the universal point over `k[X]` gives
the constant polynomial orbit. These comparisons require neither an
infinite field nor a reduced test algebra.

In prime characteristic `p`, the intersection can be taken just over the
kernels of `D_(p^r)`. For the nontrivial direction, strong induction on a
positive degree `m` reduces p-power degrees to the hypothesis. Otherwise
a consequence of Lucas's theorem supplies a nonzero intermediate binomial
coefficient. The divided-power product expresses this scalar multiple
of `D_m v` as `D_a (D_(m-a) v)`. The inner term vanishes by induction,
and cancellation of the nonzero field scalar gives `D_m v=0`.

If `n` is nonempty, the coordinate module is nonzero. The published
`Langlands.DualEigenfunctional.exists_ne_zero_forall_apply_eq_zero`
applies to the commuting p-nilpotent p-power operators and gives a
nonzero common kernel vector. The preceding comparison makes it a
nonzero vector fixed after scalar extension to every commutative test
algebra. No algebraic closedness or infinite-field assumption is used.

For an actual matrix representation `σ` of a group scheme `G` and a
supplied group-scheme morphism `f : Ga ⟶ G`, restriction gives the same
fixed-space criterion and a nonzero vector fixed by
`σ.affineAction S (x ≫ f)` for every affine test algebra and additive-group
point `x`. This follows from `MatrixRepresentation.affineAction_restrict`.
The criterion is valid over every field; the nonzero existence result
retains prime characteristic and the nonempty coordinate type.

This is derived content using the actual coefficient construction, the
proved Mathlib consequence of Lucas's theorem and the published common
kernel theorem. It assumes a supplied actual additive-group representation.
It constructs no root subgroup or Steinberg module and does not prove
`SteinbergBigCellStatement`.
