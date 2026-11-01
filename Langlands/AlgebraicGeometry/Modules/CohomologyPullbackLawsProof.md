# The five laws of canonical pullback on actual relative cohomology

The theorem `relativeCohomologyPullbackLawsStatement` proves exactly the
published `RelativeCohomologyPullbackLawsStatement.{u}`. This is the full
conjunction of identity, composition, coefficient naturality, degree-zero
normalization, and split retraction for the actual
`relativeCohomologyPullback` defined in `CohomologyPullback`.

Every component retains the arbitrary universe, every commutative base ring,
actual schemes over its spectrum, actual structure-sheaf modules, and all
natural degrees occurring in its statement, including zero. The split
component retains only its given structural equality `j ≫ m = 𝟙 X`.
There are no added geometric, flatness, acyclicity, comparison, existence,
or supplied cohomological-law hypotheses. The construction, elementary
section map, statement, and specified coefficient isomorphisms are the
published ones.

## Implemented proof

The Lean proof constructs the nested conjunction using five unconditional
component theorems in their published order. The imported component modules
contain the proofs and detailed paired explanations.

- `CohomologyPullbackIdentityProof` proves
  `relativeCohomologyPullbackIdentityStatement`. The actual adjunction unit,
  followed by the identity pushforward comparison, is the inverse
  `pullbackId` coefficient map, by the adjunction mate equation. Termwise
  identity comparisons commute with extension by zero, the actual resolution
  augmentation, and the sections comparison. Naturality of the derived unit
  then cancels the resolution comparison and identifies the derived pullback
  with the derived map of `pullbackId.inv`. Homology naturality followed by
  the specified forward `pullbackId.hom` gives the identity.
- `CohomologyPullbackCompositionProof` proves
  `relativeCohomologyPullbackCompositionStatement`. It constructs a natural
  comparison for pushforward followed by derived relative sections, whose
  factorization is fixed by the actual derived unit and termwise sections
  comparison. Equality of such transformations is checked on injective
  complexes. That comparison respects pushforward composition. Passing to
  single complexes and cancelling the chosen-resolution comparisons expresses
  the actual derived pullback as the derived image of the actual adjunction
  unit followed by this comparison. The unit's mate equation and comparison
  coherence prove composition with the inverse coefficient map; composing
  with the prescribed forward `pullbackComp.hom` gives the required law.
  The published homology comparisons transfer this equality to cohomology.
- `CohomologyPullbackCoefficientNaturalityProof` proves
  `relativeCohomologyPullbackCoefficientNaturalityStatement`. A coefficient
  morphism induces a map between the chosen injective resolutions of the
  actual pulled-back modules. The actual augmentation, termwise sections
  comparison, derived unit, and resolution comparison respect that map.
  Substituting these equations into the defining factors proves naturality
  of the actual derived pullback. Naturality of the homology comparisons
  yields precisely the coefficient square in the published statement.
- `CohomologyPullbackDegreeZeroProof` proves
  `relativeCohomologyPullbackDegreeZeroStatement`. The derived unit on a
  single complex, transported through a chosen injective resolution, has
  degree-zero homology equal to Mathlib's `toRightDerivedZero`. For the actual
  pullback augmentation, the head after the termwise sections comparison is
  exactly `relativeGlobalSectionsPullback` followed by sections of the target
  augmentation. A calculation through cycles and homology therefore gives
  the commuting square with `toRightDerivedZero`. Relative sections preserve
  finite limits, so the published `relativeCohomologyZeroIso` is its inverse.
  Cancelling these canonical comparisons proves the required normalization
  with the forward isomorphisms in the stated directions.
- `CohomologyPullbackSplitRetractionProof` proves
  `relativeCohomologyPullbackSplitRetractionStatement`. The prescribed split
  coefficient isomorphism is the composite of `pullbackComp`, `pullbackCongr`
  for the underlying equality of scheme morphisms, and `pullbackId`.
  Functoriality, the composition theorem, equality transport of the actual
  map along `j ≫ m = 𝟙 X`, and the identity theorem give its retraction
  equation in exactly that order.

The derived-unit inverses used in these component proofs are justified by
proved acyclicity of pushed-forward injective resolution terms and the
published acyclic-terms derived-unit theorem. They impose no acyclicity
assumption on an arbitrary coefficient module.

## Provenance and scope

This assembly and its exact coefficient formulas are internal consequences
of the existing scheme-module constructions and their component proofs. The
general Stacks cohomological f-map framework constructs a derived map from
an adjunction/coefficient map into the full pushed-forward injective
resolution and inverts an acyclic sections comparison. The component
explanations distinguish that framework from the exact scheme-module
coherence and normalization equations proved here; this theorem asserts no
additional comparison with a different implementation of that framework.

The full five-law conjunction is now proved for the published actual map.
The proof imports neither the translation-difference lifting result,
downstream dual or Picard existence results, nor the separate host's
cohomology-vanishing theorem. Assembly of that host is outside this result.
