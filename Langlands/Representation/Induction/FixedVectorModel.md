# A finite model for fixed vectors of smooth induction

This internal construction identifies the actual fixed vectors of smooth
induction with a finite product of coefficient fixed spaces. The ring, group,
and representation carrier have independent universes `uR`, `uG`, and `uV`.
The coefficient ring is an arbitrary commutative ring. The group is a
topological group, the subgroup `P` is arbitrary, and the actual representation
`σ : Representation R P V` need not be smooth or admissible.

For a compact open subgroup `K` and a finite set `t` containing exactly one
representative of each double coset, `fixedEvaluationEquiv` has type

```lean
fixedVectors (smoothInduced P σ) K.toSubgroup ≃ₗ[R]
  ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup)
```

Its forward linear map is the existing `fixedEvaluation P σ K t`.
Its inverse is the finite sum of the existing actual compact double-coset
sections. No finite dimensionality, Hausdorff condition, closedness of `P`,
local compactness of the ambient group, or assumption of an induced-module
isomorphism is used.

## Construction and intrinsic laws

`fixedDoubleCosetSection` takes a vector fixed by
`conjOpenSubgroup P K x`, namely the subgroup of `P` consisting of the `p`
with `x⁻¹ * p * x ∈ K`. It regards `compactDoubleCosetSection` as a fixed
vector of smooth induction. The published right invariance law verifies
membership in that actual fixed-vector submodule.

`fixedDoubleCosetSection_eval_self` gives its prescribed value at `x`.
`fixedDoubleCosetSection_eval_of_ne` shows that it vanishes at every point
belonging to a different double coset. For the latter, a nonzero value would
put the point's image in the published support bound, yielding a
factorization in `P * x * K` and hence equality of double-coset classes.

`fixedSectionSum` adds these vectors over `i : t`.
`fixedEvaluation_fixedSectionSum` states that its evaluation is the given
coefficient family whenever the map from `t` to double-coset classes is
injective. At each representative exactly its own section contributes.
Consequently `fixedEvaluation_surjective` needs distinctness but does not
need the representatives to cover the group.

`fixedEvaluation_bijective` adds the cover hypothesis and applies the
published `fixedEvaluation_injective`. `fixedEvaluationEquiv` packages
this actual bijective linear map using `LinearEquiv.ofBijective`.
`fixedEvaluationEquiv_toLinearMap` identifies the forward linear map, and
`fixedEvaluationEquiv_symm_apply` identifies its inverse with
`fixedSectionSum`. These laws remove any ambiguity from the choice-based
inverse in `LinearEquiv.ofBijective`.

## Finding representatives

`exists_finset_doubleCoset_representatives` assumes only compactness of
`LeftQuotient P` and openness of `K`. The published
`exists_finset_doubleCoset_cover` first gives a finite cover. Its image
surjects onto the double-coset quotient, so that quotient is finite.
Taking the finite image of `Quotient.out` supplies representatives.
`DoubleCoset.out_eq'` proves that they cover the group and that no two
distinct chosen points have the same class.

This existence result uses no compactness of `K`; compactness of `K` is
required for the compact sections used in the equivalence.

## Provenance and dependencies

Worker 289 implements this internal supporting construction using the
finite compact-section model proposed by Worker 34. The related
field-specific section and expansion arguments in
[`FiniteProductTensorBijectiveProof`](FiniteProductTensorBijectiveProof.md),
written by Worker 256 with proof-design contributions from Worker 321,
provided the support and finite-quotient proof routes adapted here.
Worker 34 and Worker 256 are credited as coauthors for these contributions.
The present module imports neither that tensor-product proof nor its target.

The direct project import is
[`CompactLocalSection`](CompactLocalSection.md), which imports
[`CompactQuotientProof`](CompactQuotientProof.md). The used declarations
are `compactDoubleCosetSection`, its value, support, and right invariance
laws, `conjOpenSubgroup`, `fixedEvaluation`, its injectivity theorem, and
`exists_finset_doubleCoset_cover`. Mathlib's
`Mathlib.GroupTheory.DoubleCoset` supplies the actual quotient,
`DoubleCoset.eq`, and `DoubleCoset.out_eq'`; elementary finite-sum and
linear-equivalence results finish the construction.

This unit does not use character independence, Langlands classification,
the geometric lemma, adjointness, or cuspidal support. It supplies a finite
model for a later trace comparison; it does not prove unramified regularity,
same-Levi induction independence, or the full rational exact-K0 Weyl
conjugacy target.

## Development checks

The paired module compiles with zero errors and warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Declaration inspection of
`fixedEvaluationEquiv` confirms the three independent universe parameters
`uR`, `uG`, and `uV`, with only `propext`, `Classical.choice`, and `Quot.sound`
as axioms. Compilation and declaration inspection do not establish independent
semantic acceptance or publication.
