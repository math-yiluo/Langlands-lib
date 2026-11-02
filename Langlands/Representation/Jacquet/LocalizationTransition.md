# Canonical transitions between nested localized quotients

This is an internal construction derived from the published actual quotient
and universal property in `Langlands.Representation.Jacquet.Localization`.
All declarations lie in `Langlands.Jacquet.Localization`. Author: Worker 194.

Let `U ≤ N` be actual subgroups of an arbitrary group `G`. Let `θ : U →* Rˣ`
and `η : N →* Rˣ` be characters over a commutative ring, with
`η (Subgroup.inclusion hUN u) = θ u` for every `u : U`. The carriers, the
coefficient ring and the group have independent universes. No finiteness
assumption is imposed on representations.

`transitionLinear U N hUN θ η hθη ρ` factors the quotient map for `(N, η)`
through the quotient for `(U, θ)`. It uses the existing `lift`: the
character restriction identity and `mk_apply_subgroup` prove that every
smaller-subgroup relation is killed. Its formula is precisely
`[v]_(U,θ) ↦ [v]_(N,η)`, as proved by `transitionLinear_mk` and
`transitionLinear_comp_mk`. `transitionLinear_unique` proves uniqueness
with that quotient square. `transitionLinear_surjective` follows by choosing
a representative of any target class.

`transitionLinear_natural` proves that these maps commute with every ambient
intertwiner, using the published `mapLinear` on each side.
`transitionLinear_refl` and `transitionLinear_comp` prove identity and
composition for a chain `U ≤ N ≤ P`, with compatible characters.
All these equalities are checked after the surjective first quotient map
using the existing `hom_ext`; their representative formulas agree literally.

If `M` normalizes both subgroups and preserves both characters, `transition`
packages the same linear map as an intertwiner between their descended,
unnormalized `M` actions. Equivariance is proved on representatives.
`transition_mk`, `transition_comp_quotientMap` and `transition_natural`
give the representative formula, quotient square and naturality as
equalities of intertwiners.

With any topology on `G`, `smoothTransition` bundles these components as a
natural transformation between the two existing `smoothFunctor`s. The
subgroups have the induced topologies. Smoothness of both objects is supplied
by the published functors, rather than a new input.
`smoothTransition_app_mk` records the same class formula for each component.
No continuity of multiplication or closedness hypothesis is needed here.

The intended Aubert application is the quotient part of a canonical
transition, with trivial localization characters. This unit does not
construct the surrounding normalized parabolic-induction transition.
For that application, the actual radical containments, restriction of
acting Levi groups, Haar normalization identities, and compatibility with
induction remain separate inputs to the shared general adapters. The module
introduces no alternate reductive framework and assumes no geometric
lemma, support classification, exactness of a complex, or finite-length
preservation.

The mathematical provenance of this unit is the universal property of the
explicit quotient already published in `Localization`, not an additional
literature theorem. The proof applies directly to the actual relations
`ρ u v - θ(u) • v`; there are no new axioms or proposition assumptions
encoding the desired conclusions.
