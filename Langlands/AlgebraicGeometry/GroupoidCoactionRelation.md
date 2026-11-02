# The relation-ring coaction

This internal helper constructs a coaction on `C` with its original
`B`-module structure through the source algebra map. In `C ⊗[B] C`, the
two universal relation points have the same source. Reverse the left point
and compose the right point with it. The resulting ring map `δ` has formulas
`δ(t b) = 1 ⊗ t b` and `δ(s b) = t b ⊗ 1`.

The second formula proves the required target semilinearity relative to the
source module structure. Specialization along a diagonal point gives the
identity coaction. For two composable points, specialization at the composite
agrees with the iterated coaction. Both identities are proved as ring-map
identities using that the source and target images generate `C`, via the
ring relation's `hom_ext`. A tensor ring lift packages the iterated
coaction as a ring homomorphism.

Multiplication `μ : C ⊗[B] C → C` satisfies
`μ(δ(c)) = t(identity(c))`. This equality is again proved by `hom_ext`,
using the two formulas above and the identity point of the relation.
For an invariant `c`, applying `μ` to `δ(c) = 1 ⊗ c` therefore gives
`c = t(identity(c))`. Conversely, every `t(b)` is invariant by the target
formula. These are the exact invariants for the unchanged published
invariant predicate.

The target map consequently gives `relationInvariantMap` from `B` into
the invariant submodule over `A = invariantRing t`. Its `A`-linearity
uses `t(a) = s(a)` for `a ∈ A`. The identity point is a left inverse of
`t`, so this map is injective; the invariant characterization proves
surjectivity. `relationInvariantEquiv` packages this actual map as an
`A`-linear equivalence. Its forward map is `t` and its inverse is the
identity point restricted to invariants.

The construction uses only the existing ring étale equivalence relation,
its universal-point helper and the unchanged coaction definition. Its
provenance is internal algebraic infrastructure for the Serre criterion.
It uses Mathlib's ring tensor lifts and multiplication map. No acyclicity
or Noetherian assumption is used. The conditional counit, ring pushout,
and final affine quotient argument are not proved in this module.
