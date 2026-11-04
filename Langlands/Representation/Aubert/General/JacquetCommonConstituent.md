# Common constituents from nonzero actual Jacquet modules

Worker 158 implements this derived internal construction for the full smooth
support-vanishing task. The cyclic-module construction adapts the published
argument of Workers 1210, 379 and 238 in
`Smooth.RenardIrreducibleExistenceProof`. The explicit image range restriction
and its nontriviality argument adapt the implementation of Workers 320 and 514
in `Filtration.NonzeroImageIrreducibleQuotient`; the present argument uses
unrestricted irreducible-subquotient existence after that image step.
Worker 593 coordinated the independent scope; Worker 78 confirmed that it does
not duplicate the separate irreducible Jacquet-detection task.

The namespace is
`Langlands.Aubert.General.JacquetCommonConstituent`.
`CommonConstituentData h hU E` contains an actual irreducible smooth complex
representation `levi` of `M` and an actual irreducible smooth representation
`constituent` of `G`, together with actual subquotient witnesses placing
`constituent` in both `E` and normalized induction of `levi`.

`of_nontrivial_jacquet` constructs these data when normalized Jacquet restriction
of `E` is nontrivial. Its inputs are an actual semidirect decomposition
`P = M ⋉ U` in a locally compact nonarchimedean group, closedness of `U`,
`IsUnimodularModulus U hU`, and compactness of the actual left quotient
`Induction.LeftQuotient P`. It does not restrict `E` to finite length or
admissible representations. The group and carrier parameters are independent;
`E` and both output representations have carrier universe `max uG uV`, so
normalized induction remains in that universe.

## Implemented argument

`exists_finite_subrepresentation` lifts a nonzero Jacquet class to a vector
`x` of `E` and takes its span over the actual group algebra. The smooth
subrepresentation on that span is finitely generated: its subtype map,
converted to a group-algebra linear map and corestricted to the span, is
bijective. The class of `x` in its Jacquet module is nonzero because the
Jacquet map of the inclusion carries it to the original nonzero class.
This uses `normalizedJacquetFunctor_map_mk` and needs neither exactness nor
compactness.

Compactness enters only through the published
`JacquetFiniteGeneration.finite_of_compactQuotient`: the Jacquet module of
the constructed cyclic subrepresentation is finitely generated over `ℂ[M]`.
The helper `exists_irreducible_quotient_of_moduleFinite` uses the coatomic
submodule lattice of a finitely generated module to obtain a maximal proper
subrepresentation. The published
`SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom`
makes its actual quotient irreducible. The quotient morphism is surjective,
and irreducibility makes its target nontrivial, so the morphism is nonzero.
No finite-length assertion is used or obtained in this step.

The published actual first adjointness equivalence
`FirstAdjointness.equiv` sends this nonzero quotient morphism to a nonzero
morphism from the cyclic subrepresentation to normalized induction of the
irreducible Levi quotient. Its actual smooth image is nontrivial, is an
actual quotient of the cyclic subrepresentation, and is an actual
subrepresentation of the induced object. The unrestricted
`SmoothRep.RenardIrreducibleExistence.exists_irreducible_subquotient`
gives an irreducible subquotient of this image. The published
`smoothSubquotientTransitivity` places it in both required ambient objects.
`Classical.choice` selects the resulting data.

## Scope and remaining comparisons

This is a construction from published algebraic and actual normalized-functor
APIs. It has internal provenance and makes no new claim about a literature
passage. The proof uses actual first adjointness at its stated closedness and
unimodularity scope. It uses no Langlands classification theorem, character
independence, geometric lemma, K0 equality, or Aubert Proposition 3.2.
The transitivity API imports `Classification.SupercuspidalSupport` for its
generic injective/surjective subquotient presentation; no GL cuspidal-support
existence or uniqueness theorem is applied.

The common constituent is not asserted to have nonzero Jacquet restriction.
For an application to the exact rational support-vanishing target one must
still discharge actual quotient compactness, put the irreducible Levi output
in an actual cuspidal series inside that Levi, transport its presentation by
exact normalized induction and induction transitivity, and prove the required
actual standard-index and association comparisons. This file supplies none of
those inputs and does not prove
`RationalSupportCategoryJacquetVanishingStatement`. No target or imported pair
is changed.
