# Natural Jacquet transport of the actual sharp cokernel

Worker 1300. Internal algebraic bridge for the associated-Levi comparison.
This module does not prove that comparison or its geometric ingredients.

`jacquetFunctor_mapsShortExactIntertwiners` reformats the published theorem
`jacquetFunctor_map_isShortExact`. It uses normalized Jacquet restriction on
all smooth complex representations and retains the exact premise
`Jacquet.Localization.IsLimitOfCompactSubgroups U`. It adds no finite-length,
admissibility, or finite-generation assumption. The imported proof uses
`Jacquet.Localization.characterLocalizationExactness` with the trivial
character and the actual Levi normalizer inclusion.

The `StandardComplex` wrappers use precisely `removedFamily`, the published
complement indexing, and the unchanged signed differential.
`sharpCokernelIso` specializes `Complex.terminalCokernelIso` to the retained
degree `Fintype.card ι - I.card`. Its source is the actual smooth module
cokernel of the incoming natural differential after applying the supplied
exact functor; its target is the literal published `sharpFunctor` followed
by that functor. `jacquetSharpCokernelIso` takes the actual normalized
`jacquetFunctor` at `I` and supplies its exactness using the displayed
compact-limit premise. Both comparisons commute with the mapped original
sharp projection as equalities of natural transformations.

Degree zero uses the zero incoming map, so empty root sets and full-support
terminal degree zero are included. No positive-rank assumption occurs.
The root, group and representation carrier universes retain their published
scope. There is no direct-sum or geometric-filtration comparison here:
the source is the cokernel of the mapped actual degree differential.
In particular, this construction does not replace the separate
`JacquetComplex.jacquetDegreeEquiv` degree comparison.

The provenance is specialization of the actual terminal quotient and exact
smooth cokernel construction, with the named published Jacquet exactness
theorem. No Langlands-classification, character-independence, geometric-lemma,
adjointness, or Aubert Proposition 3.2 assertion is used in these proof bodies.
