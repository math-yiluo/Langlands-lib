# Canonical standard Levi operators and Weyl data on actual rational points

Worker 29, with Worker 3640, assembles the structural data that the
published rational-point targets of the general Aubert program still take
as separate premises. The data are the standard Levi subgroups, their
restricted parabolic structure and alternating operators, and the
relative-Weyl Coxeter data. This is a derived construction supporting
Families 1 and 2 of the program. It is a companion to
`CanonicalRationalOperator` and leaves that module unchanged. No
finite-length preservation, duality identity, Jacquet or induction formula,
or corrected-complex statement is proved here, and no published proposition
or proof-task target is changed.

## Scope

The field `k : Type u` is an arbitrary nonarchimedean local field. It has
no characteristic, residue-field or universe restriction. `G` is a group
scheme over `Spec k`, connected reductive wherever `hG` appears. Then
`i : T.toGrp ⟶ G` is a maximal split torus and `ν` a generic cocharacter.
There is no splitness, quasi-splitness or positive-relative-rank
hypothesis. Index sets are finite sets of the literal actual simple-root
subtype `SimpleRoot i ν`. That subtype may be empty, and nothing here
assumes otherwise.

The topology on the actual rational-point group `RationalPoint k G.X` is
the published `RationalPointFamily.pointTopology`, as in
`CanonicalRationalOperator`. Standard Levis `levi i ν J` carry the subspace
topology. The ambient affineness and the monomorphism property of `i`
appear as section typeclass arguments `[IsAffineHom G.X.hom]` and
`[Mono i.hom.hom.left]`. Both are propositions, so any two instances agree
definitionally. In particular they agree with `hG.isAffineHom` and
`hi.isSplitSubtorus.mono`.

## Standard Levi structure

- `canonicalStandardLevi_isClosed`: every actual standard Levi is closed.
  This is `isClosed_levi_of_isNonarchimedeanLocalField`.
- `canonicalStandardLeviProjection_continuous`: for every `J` and every
  `I : Finset J`, the projection `standardLeviProjection` of the restricted
  semidirect decomposition inside `levi i ν J` is continuous. It uses the
  published `GroupScheme.standardLeviIntersection` and
  `continuous_standard_projection` with `GroupScheme.standardCocharacter`.
  This theorem does not need the local-field hypotheses, and they are
  omitted from its signature.
- `canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups`: every
  restricted radical `(unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)`
  is a limit of compact subgroups. It applies
  `standardLeviUnipotent_isLimitOfCompactSubgroups` to the published
  ambient statement.
- `canonicalStandardLeviInduction_preservesFiniteLength` and
  `canonicalStandardLeviJacquet_preservesFiniteLength`: restricted
  normalized induction and Jacquet restriction inside `levi i ν J`
  preserve finite length for every `I : Finset J`. The first uses only the
  dynamic induction input. The second uses both dynamic inputs. They apply
  `standardLeviInduction_preservesFiniteLength` and
  `standardLeviJacquet_preservesFiniteLength` to the standard-family
  transports `standardInduction_preservesFiniteLength_of_dynamic` and
  `standardJacquet_preservesFiniteLength_of_dynamic`. These two theorems
  keep the ambient local-compactness and nonarchimedean typeclass arguments
  of the published helpers. The Hausdorff argument is unused and omitted.

## The canonical Levi operator

`canonicalRationalLeviAlternatingOperator hG i ν hi hν hiFl hrFl J` is the
unadjusted Aubert operator of the actual standard Levi `M_J` on its exact
`FiniteLengthGrothendieckGroup` of smooth complex representations, at
carrier universe `max (u + 1) v`. It specializes the published
`rationalLeviAlternatingOperator` with the following inputs:
- `standardLeviIntersection`;
- `canonicalStandardUnipotent_isClosed` (from `CanonicalRationalOperator`);
- `standardParabolic_isClosed_of_standardCocharacterStatement`;
- the closed Levi, projection, compact-limit and finite-length theorems
  above.

The ambient topological properties are supplied inside the definition, as
in `canonicalRationalAlternatingOperator`. They are
`BruhatTits.localField_t2Space`, `rationalPoint_locallyCompactSpace`,
`Plancherel.rationalPoints_nonarchimedeanGroup` and
`rationalPoint_t2Space`, with affineness and smoothness from `hG`.

Exactly two representation-theoretic inputs remain, and both are explicit
arguments: `hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}`
and `hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}`. They
are the existing general targets for normalized dynamic induction and
Jacquet restriction. They are neither asserted nor proved here.

## Comparison with the published operators

Every argument of the published operators other than the group data is a
proposition. Both comparisons below are therefore proved by `rfl`, using
definitional proof irrelevance.

- `rationalLeviAlternatingOperator_eq_canonical`: for any local-compactness,
  nonarchimedean and Hausdorff instances and any premises `hInter`, `hU`,
  `hP`, `hM`, `hproj`, `hUc` and per-index finite-length premises,
  `rationalLeviAlternatingOperator` on `levi i ν J` equals
  `canonicalRationalLeviAlternatingOperator hG i ν hi hν hiFl hrFl J`.
- `rationalAlternatingOperator_eq_canonical`: likewise, for any premises
  `hStandard`, `hU`, `hP`, `hproj`, `hUc`, per-index finite-length premises
  and `hRoots`, `rationalAlternatingOperator` equals Worker 3640's
  `canonicalRationalAlternatingOperator hG i ν hi hν hiFl hrFl`.

The dynamic inputs `hiFl` and `hrFl` on the right are arbitrary. So these
comparisons only rewrite an existing premise-taking operator into canonical
form. They do not derive the dynamic statements from per-index premises.

## Relative Weyl and Coxeter data

This section takes no representation inputs.

- `canonicalPointNormalizerComparison` and
  `canonicalPointCentralizerComparison` are the two components of the
  published `rationalWeylComparison`. The scheme-normalizer points of `i`
  equal the normalizer of the actual point image `torusPoints i`. The
  scheme-centralizer points equal its full centralizer `Z_G(T₀)`. The Weyl
  group `Weyl i` is the published normalizer/full-centralizer quotient of
  the actual point image. Its denominator is not replaced by the torus.
- `canonicalPointCoxeterData` is
  `rootSpanPointCoxeterData i ν hN hZ hG hi (relativeRootSystem k G hG T i hi) hν`
  for these two comparisons. It is the choice of finite actual point
  Coxeter data built from the published relative root system.
  `canonicalCoxeterMatrix` and `canonicalCoxeterSystem` are its matrix,
  indexed by the actual simple roots, and its Coxeter system on `Weyl i`.
- The following are the stored fields of these data:
  - `canonicalWeyl_finite` and `canonicalSimpleRoot_finite`;
  - `canonicalRootLengthComparison` (the root-sign length law);
  - `canonicalSimpleReflectionPairingInvariance`;
  - `canonicalLeviWeylIdentification` (the actual Weyl groups of the
    standard Levis are the standard parabolic subgroups).
- `canonicalWeylFintype` is the `Fintype` structure obtained from
  finiteness by `Fintype.ofFinite`.
- `canonicalPositiveSimpleReflectionComparison` is
  `positiveSimpleReflectionComparison_of_rootLength`.
  `canonicalMinimalityLengthCriterion` is `minimalityLengthCriterion_proof`.
- For arbitrary `Fintype` structures on `SimpleRoot i ν` and `Weyl i`:
  - `canonicalAssociatedSubsetLaws` is `associatedSubsetLaws_proof`;
  - `canonicalAssociatedLeviConjugation` is
    `associatedLeviConjugation_of_standard` with the published
    `GroupScheme.standardLeviConjugation`. It states that conjugation by
    any lift of the longest representative `w_J` carries the actual Levi of
    the associated subset onto the actual Levi of `J`.

This is the data that `rationalCorollary110bFromRankOneInputs` builds
locally from its own premises. Here it is built once, from published
theorems only.

## Provenance

This is a derived assembly. Its mathematical content is the standard
structure theory of standard parabolic subgroups, Levi subgroups and the
relative Weyl group of a connected reductive group over a nonarchimedean
local field, used throughout Aubert (1995), Section 1. That content is
already formalized in the named published declarations. This module adds no
new literature translation. It only fixes canonical choices of these
published proofs and records that the existing premise-taking operators
agree with the canonical ones.
