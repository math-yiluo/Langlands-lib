# Finite local bases and prescribed rank for smooth differentials

The theorem `Langlands.Scheme.smoothDifferentialsFiniteLocalBasisRank` proves
`Langlands.Scheme.SmoothDifferentialsFiniteLocalBasisRankStatement` in arbitrary
universe `u`. For every scheme morphism `f : X ⟶ S`, geometric smoothness gives
one local generating datum for `relativeDifferentials f` that is both locally
free and finite type. For every `n : ℕ`, geometric smoothness of relative
dimension `n` gives `Modules.IsLocallyFreeOfRank (relativeDifferentials f) n`.
There are no additional hypotheses. The proof imports the canonical affine-chart
comparison from `Langlands.AlgebraicGeometry.RelativeDifferentialsAffineChart`.
The existing target, the sheafification-based differential sheaf, and its
universal derivation are unchanged.

## Implemented neighborhood assembly

`localFreeIsoOfRestrict` converts a free trivialization of `M.restrict U.ι`
on the open subscheme into a free trivialization of `M.over U` on the
site over `U`. It uses `Scheme.Modules.overEquiv`, `overFunctorEquiv`, the
unit isomorphism of that equivalence, and `SheafOfModules.mapFreeIso`.
The equivalence preserves coproducts and the structure module, so it preserves
the free sheaf on the same index type.

`generatorsOfRestrict` transports the free sheaf's generating sections along
that isomorphism. Its canonical map from the free sheaf is an isomorphism.
`generatorsOnCover` uses a neighborhood `U x` for each point `x` as a cover;
`Opens.coversTop_iff` supplies the site covering condition. Its freeness and
finite-type properties concern this one datum, preserving the identical basis
index type at each point. `finiteLocalBases_of_neighborhoods` packages these
facts, allowing the finite basis size to vary with the point.

`fixedRank_of_neighborhoods` uses the same cover construction with index type
`ULift (Fin n)` on every neighborhood. The equivalence `Equiv.ulift` supplies
exactly the witness required by `Modules.IsLocallyFreeOfRank`. Empty schemes
are covered by the empty point-indexed family. No rank uniqueness or global
constant rank is asserted without the prescribed-rank hypothesis.

## Implemented algebraic bases

`standardSmooth_basis` obtains a finite submersive presentation from
`Algebra.IsStandardSmooth.out`. Mathlib's `SubmersivePresentation.basisKaehler`
is a basis of the actual algebraic Kähler module, indexed by the complement
of the range of the presentation's injection of relation indices into
variable indices. This complement is finite. Reindexing by `ULift` places
the index in universe `u`.

`standardSmooth_basis_rank` uses the presentation supplied by
`Algebra.IsStandardSmoothOfRelativeDimension.out`. The cardinality of that
complement equals the number of variables minus the number of relations,
which is the presentation dimension and hence the given `n`. Reindexing the
basis along this cardinality equality produces a basis on `ULift (Fin n)`.
This argument works even over the zero ring: it uses the specified
presentation dimension and does not invoke rank uniqueness or a nontriviality
hypothesis.

## Differential assembly and published dependencies

For the first target clause, `Smooth.exists_isStandardSmooth` supplies an
affine neighborhood of each point and a standard-smooth chart algebra.
For the second clause,
`SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`
supplies the corresponding prescribed-dimensional chart algebra. Both use
exactly `(f.appLE U V e).hom.toAlgebra` as the algebra structure.

The published `relativeDifferentialsAffineChartBasisIso f hU hV e I b`
transports each algebraic basis to a free trivialization of the restriction
of the actual differential sheaf. That definition composes the unconditional
`relativeDifferentialsAffineChartIso` with
`relativeDifferentialsAffineChartModelBasisIso`. The comparison itself uses
the published open-immersion locality and Spec-comparison invertibility
proofs. Its source is the actual restricted sheaf and its target is the tilde
model for precisely the chart ring map. Thus no comparison, invertibility,
quasi-coherence, or differential-rank premise remains in this theorem.

The neighborhood assembly then proves both target clauses using the same
finite local generating datum for freeness and finite type. The only public
declaration added by this module is the exact-target theorem; all auxiliary
constructions and lemmas are private.

## Source and provenance

The retained source `stacks-smooth-differential-rank-2026-10-22`, folder SHA256
`a20ebb3b9b37ee166cb66decf78eed5aae44e5ed93634cf911eee19d224c1bc5`,
`01V4.html`, Lemma 29.35.12 (02G1), its proof, and Definition 29.35.13 (02G2)
were read. The lemma reduces finite local freeness and rank to standard-smooth
affine charts. Its relative-dimension definition uses differential rank;
Mathlib's geometric predicate instead supplies standard-smooth presentations.
The implemented presentation-basis argument is the bridge from that predicate
to the required basis size. This theorem does not assert the source's additional
pointwise fibre-dimension equality, which is not part of the assigned target.

The over-category and cover packaging are internal consequences of Mathlib's
module-sheaf equivalences and free-sheaf universal property. The algebraic
basis is reused from Mathlib, pinned by environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`; no algebraic freeness theorem or geometric
comparison is invented. Worker 124 authored this assembly. The chart model, unconditional comparison,
and basis transport are imported published work by Worker 310; his
coordination supplied their interface.
