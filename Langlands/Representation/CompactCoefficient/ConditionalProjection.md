# Conditional equivariant isotypic projections

Worker 173 constructs projections from **supplied complementary invariant
subspaces** and specializes them to the published intrinsic isotypic and
annihilator subspaces. This is an internal algebraic construction and its
elementary laws. It does not prove that the intrinsic subspaces are
complementary, or that compact-isotypic projectors exist without that input.

## Construction and general laws

`Langlands.projection_natural_of_mapsTo` concerns modules over a ring, with
independent source and target carrier universes. Given complementary pairs
`S,Q` and `S',Q'` and a linear map `f` mapping each source summand into its
corresponding target summand, it proves

\[
f\,\operatorname{pr}_{S,Q}(v)
=\operatorname{pr}_{S',Q'}(f(v)).
\]

The projections are Mathlib's `Submodule.projection`. The proof writes
`v=s+q` using `existsUnique_add_of_isCompl`. The source projection fixes `s`
and kills `q`; the target projection fixes `f(s)` and kills `f(q)`.

For a representation `ρ` of a monoid over a commutative ring,
`Langlands.equivariantProjection S Q h` bundles this linear projection as
an actual `Representation.IntertwiningMap`. Here `S` and `Q` are actual
subrepresentations and `h : IsCompl S.toSubmodule Q.toSubmodule` is required.
Its equivariance follows by applying the preceding naturality law to each
group action map, which preserves both invariant subspaces.

The suffixes `_range`, `_ker` and `_idempotent` give the exact invariant
range `S`, kernel `Q`, and idempotence of the underlying linear endomorphism,
using the corresponding Mathlib projection results.
`equivariantProjection_natural` gives the same naturality identity for an
actual intertwiner mapping both invariant summands into their counterparts.
`equivariantProjection_unique` says every supplied equivariant idempotent
with range `S` and kernel `Q` equals the construction. It applies Mathlib's
`LinearMap.IsIdempotentElem.ext_iff` to the underlying linear maps.

## Intrinsic isotypic specialization

The remaining declarations are in `Langlands.CompactCoefficientClass`.
Fix a group `G : Type uG` with a topology and
`c : CompactCoefficientClass.{uG,uV} G`. Let
`A : SmoothRep.{0,uG,uW} ℂ G` and
`B : SmoothRep.{0,uG,uX} ℂ G`.
The group, representative, source-carrier and target-carrier universes
`uG,uV,uW,uX` are independent. The class representative universe stays fixed
throughout a naturality statement; no comparison between different
representative universes is asserted.

`isotypicProjectorOfIsCompl c h` specializes the general construction to
`isotypicSubrepresentation c A` and `annihilatorSubrepresentation c A`.
The input `h` asserts that these two underlying submodules are complementary.
The suffixes `_range`, `_ker`, and `_idempotent` record the corresponding
exact laws.

`isotypicProjectorOfIsCompl_natural` requires complementarity in both `A`
and `B` and proves naturality along every actual intertwiner `f : A → B`.
It uses the already published `mapsTo_isotypicSubrepresentation` and
`mapsTo_annihilatorSubrepresentation` laws, which allow independent ambient
carrier universes.

`isotypicProjectors_natural` starts instead with any supplied equivariant
idempotents `P` and `Q` on `A` and `B`, and exact identifications of each
range and kernel with its intrinsic isotypic and annihilator subspaces.
Idempotence implies range/kernel complementarity. Uniqueness identifies
both endomorphisms with the conditional construction, and its naturality
gives `f (P v) = Q (f v)`.

## Provenance and scope

All constructions and proofs are internal algebraic consequences of
Mathlib's `LinearAlgebra.Projection` and `RepresentationTheory.Intertwining`,
and the published Library `CompactCoefficient.Isotypic` definitions and
MapsTo laws. No literature theorem is asserted or used as an unproved input.
No published source pair is changed.

There is no Haar, admissibility, finite-dimensionality or finite-length
assumption because the only existence input here is explicit
complementarity. Establishing that input under the intended topological
group hypotheses remains a separate mathematical obligation. This module
also proves no orthogonality between different classes, compact coefficients
of the range, fixed-level vanishing, class transport under group
automorphisms, or final product-Levi decomposition.
