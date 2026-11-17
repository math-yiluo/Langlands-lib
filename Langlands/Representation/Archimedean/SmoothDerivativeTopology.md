# Genuine word-derivative topology on smooth vectors

Authors: Worker 779 (draft) and Worker 723. This internal prerequisite
to Task 7293 equips a dedicated copy of the published smooth vectors
with the topology induced by all genuine word derivatives. It proves
continuity of the derived operators, identifies the topology with the
one given by the genuine word seminorms, and shows that the published
finite-word continuity predicate is exactly continuity for this
topology. It also extends a functional on any complex submodule with
exactly a supplied finite word bound.

## Carrier and topology

The setting is that of the companion `SmoothDerivative`: a real smooth
Lie group `[LieGroup I ∞ G]`, a complex normed space `E`, and a
homomorphism `π : G →* (E →L[ℂ] E)`. The four universe parameters remain
independent. No completeness or joint action continuity is assumed.

In `Langlands.Archimedean`, `DerivativeSmoothVectors I π` is a dedicated
copy of `smoothVectors I π`. It carries the inherited additive group,
complex and real module structures and scalar tower.
`DerivativeSmoothVectors.toSmooth` is the complex-linear equivalence to
the published smooth-vector space; no continuity of this equivalence
to an independently chosen topology is asserted.

`DerivativeSmoothVectors.derivativeCoordinates` is the complex-linear
map into the product `List 𝔤 → E` sending `v` to
`Xs ↦ iteratedLieDerivative I π Xs (toSmooth I π v)`. It is injective
because the empty word is the underlying vector. The topology on the
copy is induced by this map from the product topology. The module supplies
instances for a Hausdorff topological additive group, continuous real
and complex scalar multiplication, and a locally convex real space.
Each of these structures is pulled back from the product space through
the injective linear coordinate map, using Mathlib's induced-topology
instances (`IsInducing.isTopologicalAddGroup`, `continuousSMul_induced`,
`IsEmbedding.t2Space`, `LocallyConvexSpace.induced`).

`DerivativeSmoothVectors.derivativeCLM I π Xs` continuously selects one
word derivative, valued in the original normed space `E`.
`tendsto_iff_derivativeCoordinates` states, for any filter and any map
into this copy, that convergence to `v` is equivalent to convergence in
`E` of each genuine word derivative to that of `v`. This is product
convergence pulled back along the embedding.

`DerivativeSmoothVectors.wordSeminormFamily I π` is the family, indexed
by all words `Xs : List 𝔤`, of the companion's `wordSeminorm I π Xs`
precomposed with `toSmooth`; its evaluation lemma gives
`‖iteratedLieDerivative I π Xs (toSmooth I π v)‖`.
`withSeminorms_wordSeminormFamily` proves Mathlib's `WithSeminorms`
for this family: the induced topology is exactly the topology generated
by the genuine word seminorms. The proof compares neighbourhood filters
of zero. The induced neighbourhood filter is the pullback of the product
neighbourhood filter, which is the infimum over words of pullbacks by
the coordinate projections; the neighbourhood filter of zero in `E` is
the pullback of that of `0 : ℝ` by the norm. Composing the pullbacks
gives the infimum of the pullbacks by the word seminorms, which is
Mathlib's criterion `SeminormFamily.withSeminorms_iff_nhds_eq_iInf`.

## Derived operators and finite bounds

`DerivativeSmoothVectors.operator I π X` transports the genuine
`smoothLieDerivative` through `toSmooth`. Applying its `Xs` coordinate
gives the original vector's `Xs ++ [X]` coordinate. This follows from
the companion's word-concatenation identity; it respects the convention
`[X₁,…,Xₖ] ↦ dπ(X₁) ⋯ dπ(Xₖ)`. Reindexing the continuous coordinates
proves `continuous_operator`, and `operatorCLM` bundles the resulting
continuous complex-linear operator. The simp lemmas `toSmooth_operator`
and `operatorCLM_apply` record that, after forgetting the topology,
`operatorCLM I π X` acts as `smoothLieDerivative I π X`.

`continuous_of_isContinuousOnSmoothVectors` proves one direction of the
bridge to the existing predicate. If a complex-linear
functional `L` on `smoothVectors I π` satisfies
`IsContinuousOnSmoothVectors I π L`, then
`v ↦ L (toSmooth I π v)` is continuous for the induced topology.
The predicate supplies finite `S` and real `C` with

`‖L v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs v‖`.

The finite sum on the right is continuous and vanishes at zero. Squeezing
the norm of the linear functional proves continuity at zero, and
linearity gives continuity everywhere.

`isContinuousOnSmoothVectors_of_continuous` proves the converse: if
`v ↦ L (toSmooth I π v)` is continuous on the dedicated copy, then
`IsContinuousOnSmoothVectors I π L` holds. The composite of the norm on
`ℂ` with this functional is a continuous complex seminorm, so Mathlib's
`Seminorm.bound_of_continuous`, applied with
`withSeminorms_wordSeminormFamily`, gives a finite set `S` of words and
`C : ℝ≥0` with that seminorm bounded by `C` times the supremum over `S`
of the word seminorms. The supremum is at most the sum over `S`
(`Seminorm.finset_sup_apply_le` and `Finset.single_le_sum`), which gives
the published bound with real constant `C`.
`continuous_iff_isContinuousOnSmoothVectors` combines both directions
into an equivalence.

## Extension with a prescribed bound

`exists_extension_of_word_bound` takes a complex submodule
`V : Submodule ℂ (smoothVectors I π)`, a complex-linear functional
`ℓ : V →ₗ[ℂ] ℂ`, a finite set `S : Finset (List 𝔤)`, and a real
`C ≥ 0`. Its hypothesis bounds every `v : V` by the displayed finite
sum with the same `S` and `C`. Its conclusion supplies a complex-linear
functional `L` on all smooth vectors such that:

- `L v = ℓ v` for every `v : V`;
- the same finite bound holds on every smooth vector;
- `IsContinuousOnSmoothVectors I π L` holds.

The proof forms the complex seminorm
`p = C • ∑ Xs ∈ S, wordSeminorm I π Xs`, using `C` as a nonnegative
real scalar. The evaluation formula for `wordSeminorm` identifies
`p(v)` with the required right-hand side. Mathlib's complex
Hahn–Banach theorem
`Module.Dual.exists_extension_of_le_seminorm` extends `ℓ` while preserving
this bound. The witnesses `S` and `C` then prove the existing continuity
predicate. Combined with `continuous_of_isContinuousOnSmoothVectors`,
this makes the extension continuous on the dedicated copy; no separate
lemma states that consequence.

## Provenance and scope

This is internal derived infrastructure built from the published orbit
derivatives, the companion's proofs that those derivatives preserve
smooth vectors and are linear, Mathlib's induced/product topology
constructions, its `WithSeminorms` theory for locally convex topologies,
and its seminorm form of complex Hahn–Banach. It is not a
formal identification with the Schwartz topology of a space of orbit
maps and makes no claim that the original smooth-vector subspace's
inherited norm topology equals this topology.

The extension is existential. Neither density nor uniqueness of the
extension is assumed or concluded. Equivariance, even for an invariant
submodule with an equivariant initial functional, is not concluded.
Applying this infrastructure to actual cuspidal Whittaker coefficients
still requires compatible smooth Hilbert globalizations, genuine
derivative and norm comparisons, and the relevant density and
equivariance arguments. No unconditional multiplicity-one theorem is
proved here.
