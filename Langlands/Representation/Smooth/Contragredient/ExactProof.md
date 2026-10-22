# Reversal of short exact sequences by smooth contragredients

`Langlands.smoothContragredientShortExact` proves the complete published
`Langlands.SmoothContragredientShortExactStatement`. For an injective intertwiner
`f : rho -> sigma` and a surjective intertwiner `g : sigma -> tau` with
`Function.Exact f g`, the reversed smooth contragredient sequence is injective,
exact at the middle, and surjective. The theorem assumes smoothness of `rho`
and `sigma` and that every open subgroup of the topological group contains a
compact open subgroup.

The group and the three representation carriers have four independent
universes. The closing declaration preserves the statement's full outer
telescope: group carrier, group structure, topology, then each carrier followed
by its additive-group and complex-module instances. The topological-group
instance, cofinality, representations, smoothness, and exactness hypotheses
are introduced inside the proposition. No topology on the modules,
admissibility, finite-dimensionality, Hausdorffness, local compactness,
countability, or smoothness assumption on `tau` is added.

## The three component lemmas

`contragredientMap_injective_of_surjective` works over any commutative
coefficient ring. If two smooth functionals have equal pullbacks along a
surjective intertwiner, evaluate that equality at a preimage of each vector.
Linear-map and subtype extensionality then identify the functionals.
Representation smoothness and compactness are not needed.

`contragredientMap_exact_of_surjective` also works over any commutative ring.
Given a smooth functional `ell` on the middle representation whose pullback
along `f` vanishes, exactness shows that `ell` annihilates `ker g`.
Mathlib's `LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective`
produces an algebraic functional `m` on the last representation with
`m (g w) = ell w`.

Choose an open subgroup fixing `ell`. For an element `k` of that subgroup
and any vector `x`, surjectivity writes `x = g w`. Equivariance of `g` at
`k⁻¹` rewrites the value of the dual action on `m` as the value of `ell`
on the corresponding translate of `w`. Fixedness of `ell` gives equality.
Thus the same open subgroup fixes `m`, so it belongs to the smooth dual and
its smooth pullback is `ell`. Conversely, any functional pulled back along
`g` vanishes on `f` because `g (f v) = 0`. This proves both directions of
middle exactness without assuming any of the three representations smooth.

`contragredientMap_surjective_of_injective_of_compact_cofinal` uses complex
coefficients and smoothness of the source and target of `f`. Given a smooth
source functional, choose an open subgroup fixing it and then a compact open
subgroup `K` inside that subgroup. The functional is therefore `K`-fixed.
The restriction `fixedVectorsMap f K.toSubgroup` is injective, by injectivity
of `f` and subtype extensionality.

Mathlib's `LinearMap.dualMap_surjective_of_injective` extends the restriction
of the given functional from the source fixed space to the target fixed
space. Surjectivity of the published
`smoothDualFixedRestriction_bijective` for the target representation lifts
this extension to a `K`-fixed smooth target functional. Its pullback and the
original functional have equal restrictions to the source fixed space:
evaluate the two extension equations at each fixed vector. Injectivity of
`smoothDualFixedRestriction_bijective` for the source representation then
identifies the two `K`-fixed smooth functionals. Taking their underlying
values supplies the required smooth preimage.

The closing theorem combines these three lemmas, applying the first to `g`,
the second to `(f,g)`, and the third to `f`. All component lemmas remain in
this module. The general-ring descent argument is distinct from the
complex-vector-space extension argument; the latter does not assert
surjectivity over arbitrary coefficient rings.

## Source and scope

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter II: *Smooth representations*, revision June 16, 2019, Section 3,
page 6, Corollary II.3.3 states reversal of short exact sequences for
admissible representations with free fixed spaces. Proposition II.3.1 on
the same page identifies compact-open fixed smooth functionals with the
algebraic dual of the original fixed space. The source's stronger ambient
conventions appear on page 1.

This proof establishes the published target's derived strengthening over the
complex numbers. Algebraic functionals extend across injective maps of
complex vector spaces without a finite-dimensionality assumption; combining
that fact with compact-open fixed duality gives the final component.
The first two components are direct algebraic pullback and smooth descent.
Only the explicit compact-open cofinality is used to choose `K`; the
source's stronger ambient hypotheses are unnecessary for this argument.

Literature ID: `casselman-2019-smooth-representations`.
Original PDF SHA256:
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The retained original is indexed under this literature ID in the project
literature collection.

## Imports and authorship

The statement is imported from
`Langlands.Representation.Smooth.Contragredient.ExactStatement`.
`Langlands.Representation.Smooth.Contragredient.CompactDualityProof` provides
`smoothDualFixedRestriction_bijective`, and
`Langlands.Representation.Smooth.FixedVectors.Definitions` provides
`fixedVectorsMap`. Their published dependencies construct the algebraic dual,
smooth part, smooth contragredient, fixed-functional restriction, and finite
compact-subgroup averaging. Mathlib's `LinearAlgebra.Dual.Lemmas` supplies the
annihilator and extension results. No admissible-duality or Hom-duality proof
is imported.

The imported project modules and their paired Markdown are published Library
dependencies and are used unchanged. In particular, compact-open fixed duality
is supplied by `Langlands.Representation.Smooth.Contragredient.CompactDualityProof`.

Worker 0 authored the complete Lean proof and initial explanation. Worker 5
verified the implementation, source correspondence and published imports,
and expanded this explanation. The Lean proof is reused byte-for-byte from
Worker 0's shared proof of `Langlands.SmoothContragredientShortExactStatement`.

The pinned environment is Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Development compilation and direct
checking of the unapplied theorem's complete type are distinct from formal
Lake validation, exact-target inspection, independent semantic review and
publication.
