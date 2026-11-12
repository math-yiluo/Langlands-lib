# Proof of reciprocal actual Haar characters on opposite rational-point radicals

Author: Worker 4204.

Module `Langlands.Representation.Aubert.General.RationalOppositeHaarReciprocityProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

## Result

`rationalOppositeHaarReciprocity : RationalOppositeHaarReciprocityStatement.{u}`
proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalOppositeHaarReciprocityStatement`
at an arbitrary universe `u`. The theorem has no parameters or premises beyond those of
the proposition. The proposition and its Markdown are unchanged.

So the statement holds as published. Let `k` be any nonarchimedean local field,
including positive characteristic. Let `G` be any connected reductive group over `k`,
`i` an actual maximal split torus and `ν` a generic cocharacter. Give `G(k)` the
canonical `pointTopology` with the displayed topology hypotheses, and assume the
displayed `StandardCocharacterStatement`. Let `I` be any finite simple-root subset,
possibly empty, with closed standard radical, and `ζ` any standard cocharacter for
`rootSet i ν I`. Then for every `m` in the literal standard Levi `levi i ν I`,

`closedRestrictCharacter (unipotent i ν I) hU (levi i ν I) _ m *
  closedRestrictCharacter (oppositeUnipotent i ζ) _ (levi i ν I) _ m = 1`.

The closedness and normalizer witnesses in this product are exactly the ones the
statement displays. These are `hU`, `isClosed_oppositeUnipotent_localField i ζ`, and the
two `.levi_le_normalizer` fields of
`isSemidirectDecomposition_of_standardCocharacterStatement` and
`opposite_isSemidirectDecomposition`.

## Implemented proof

Write `χ₀ = CommGroupScheme.groupHom ζ ≫ i` and
`χ = Dynamic.inverseCocharacter χ₀`.

1. *Instances.* `hG.isAffineHom` and `hi.isSplitSubtorus.mono` give the instances the
   statement binds, and `G(k)` gets `pointTopology`. The Hausdorff property of `k`
   comes from `Langlands.BruhatTits.localField_t2Space k`, as in
   `isClosed_oppositeUnipotent_localField`.
2. *Standard comparisons.* The displayed premise `hStandard` is applied at
   `rootSet i ν I` (with `rootSet_subset i ν I`) and at the given witness `ζ`. It gives
   `standardLevi i ν (rootSet i ν I) = Dynamic.centralizer χ₀` and
   `standardUnipotent i ν (rootSet i ν I) = Dynamic.unipotent χ₀`.
   The parabolic comparison is not used.
3. *The three subgroups as dynamic subgroups of `χ`.* Evaluated on the identity test
   scheme:
   - `unipotent i ν I` is `(Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier _`.
     This follows from `Dynamic.inverseCocharacter_inverseCocharacter` and the unipotent
     comparison.
   - `levi i ν I` is `(Dynamic.centralizer χ).carrier _`. This follows from
     `Dynamic.centralizer_inverseCocharacter` and the Levi comparison.
   - `oppositeUnipotent i ζ` is `(Dynamic.unipotent χ).carrier _`. This holds by the
     definition of `oppositeUnipotent` (`rfl`).
4. *Reciprocity.* The published theorem
   `dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus` is applied to the
   cocharacter `χ`, with these three equalities and the closedness witnesses `hU` and
   `isClosed_oppositeUnipotent_localField i ζ`. Its normalizer arguments are arbitrary
   proofs, so it accepts the statement's `.levi_le_normalizer` witnesses. Its two
   structural premises are discharged unconditionally:
   - `RelativeRootReflectionExistenceStatement.{u}` by
     `relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization`;
   - `CentralSplitTorusCharacterStatement.{u}` by `centralSplitTorusCharacter`.

   It gives the required product identity at the given `m ∈ levi i ν I`.

So the identity holds on the whole literal Levi. Nothing is restricted to a split torus,
a central component or a chosen contracting element. No reciprocal-character,
determinant, root-system, Cartan-covering, unimodularity or adapted-basis premise is
added to the theorem. The only premises used are the statement's own.

## Mathematical route of the imported reciprocity

The argument behind
`dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus` is as follows. It is
described only so that the dependencies are visible; this module does not re-prove it.

- `dynamicOppositeHaarReciprocity_of_leviAdjoint` uses `cocharacterMaximalSplitTorus`
  to write `χ` through a maximal split torus. It takes Lie coordinates from
  `dynamicAdjointDeterminantStructure`. The proved `dynamicUnipotentHaarDeterminant`
  expresses each Haar scaling factor as the normalized absolute value of the adjoint
  determinant character on the Lie algebra of the dynamic radical. Hence the product
  is `1` once the two determinant characters add to zero.
- `leviAdjointDeterminantReciprocity_of_structure` proves this vanishing. It uses
  reflection data, central split torus detection, and the proved
  `dynamicCentralizerReductive`. On the maximal split torus, lifted into the Levi, the
  two determinant characters restrict to the positive weight sums for `ζ` and `-ζ`.
  These sums are opposite because reflection data make the weight spaces of `α` and
  `-α` equally dimensional (`RelativeRootReflectionData.positiveWeightCharacter_neg`).
  If the sum of the determinant characters were nonzero, `centralSplitTorusCharacter`
  would give a central split torus of the reductive Levi on which it is nonzero. That
  torus factors through the maximal split torus, where the sum vanishes, which is a
  contradiction.

This is a different route from Renard 2026, V.5.4, printed pp. 126–127, which uses a
root-product computation on the split component and the Cartan decomposition of the
Levi. The conventions are as in the statement Markdown. The Library character
`closedRestrictCharacter` is the forward volume scaling factor, inverse to Renard's
`δ_N`, and inverting both factors preserves reciprocity.

## Declaration-level dependencies

Used directly in the proof:

- `Langlands.Aubert.General.RationalPointFamily.RationalOppositeHaarReciprocityStatement`
  (target; module `...General.RationalOppositeHaarReciprocityStatement`).
- `Langlands.Aubert.General.RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus`
  (module `Langlands.Representation.Aubert.General.DynamicOppositeHaarReciprocity`).
- `Langlands.GroupScheme.relativeRootReflectionExistence_of_rootRankOneFactorization`
  (module `Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction`).
- `Langlands.GroupScheme.rootRankOneFactorization`
  (module `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`).
- `Langlands.GroupScheme.centralSplitTorusCharacter`
  (module `Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof`).
- `Langlands.GroupScheme.Dynamic.inverseCocharacter_inverseCocharacter`,
  `Langlands.GroupScheme.Dynamic.centralizer_inverseCocharacter`,
  `Langlands.Aubert.General.RationalPointFamily.oppositeUnipotent` and
  `Langlands.Aubert.General.RationalPointFamily.isClosed_oppositeUnipotent_localField`
  (module `Langlands.Representation.Aubert.General.RationalOppositeParabolic`).
- `Langlands.Aubert.General.RationalPointFamily.rootSet_subset` (module
  `Langlands.Representation.Aubert.General.RationalPointFamily`) and the
  `StandardCocharacterStatement` premise (the statement's own binder).
- `Langlands.BruhatTits.localField_t2Space`
  (module `Langlands.BruhatTits.Unipotent.RationalPointCompactOpen`).

Main transitive proved inputs, through the theorem above:
`dynamicOppositeHaarReciprocity_of_leviAdjoint`,
`leviAdjointDeterminantReciprocity_of_structure`, `dynamicCentralizerReductive`,
`dynamicUnipotentHaarDeterminant`, `dynamicAdjointDeterminantStructure`,
`cocharacterMaximalSplitTorus` and `RelativeRoot.kernelCentralizerComponentReductive`.

A development check reported the axioms `propext`, `Classical.choice` and `Quot.sound`
only. There is no `sorry` and no new axiom.

## Scope

This module proves only the full-Haar reciprocity premise. It does not prove the
complex inverse-half scalar step, opposite-Jacquet naturality or duality, a parabolic
modular character, or ambient or Levi unimodularity. It does not prove the universal
`StandardCocharacterStatement`, which remains a displayed premise of the target.
