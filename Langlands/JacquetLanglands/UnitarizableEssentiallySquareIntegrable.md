# Essentially square-integrable representations with a unitary central character

The module `Langlands.JacquetLanglands.UnitarizableEssentiallySquareIntegrable` proves that an
essentially square-integrable representation of `GL_n(F)` with a unitary central character is
square-integrable modulo the center. Here `F` is a nonarchimedean local field (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, any characteristic) and
`0 < n`. The predicates are those of `Langlands.JacquetLanglands.EssentiallySquareIntegrable`:

- `IsSquareIntegrable ρ`: for every Borel Haar measure `μ` on `GL_n(F)/Z`, `ρ` is admissible
  and has a `UnitaryCentralCharacter` for which the absolute matrix coefficients of
  smooth-dual vectors are square-integrable on `GL_n(F)/Z`;
- `IsEssentiallySquareIntegrable ρ`: some real `s` makes
  `realPowerTwist (determinantNorm F n) (-s) ρ`, that is `ρ ⊗ |det|^{-s}`, square-integrable
  modulo the center. Here `determinantNorm F n` is `g ↦ |det g|` for the residue-normalized
  absolute value `LocalField.residueNormalizedAbsoluteValue F`.

## Declarations

- `uniformizerScalarCenter F n`: the scalar matrix of the uniformizer
  `LocalField.uniformizer F` (an element of order one, module
  `Langlands.LocalField.ResidueNormalization`), as an element of the center of `GL_n(F)`
  (`GeneralLinear.scalarToCenter`).
- `determinantNorm_uniformizerScalarCenter_ne_one`: for `0 < n`, `|det|` of this central
  element is not `1`.
- `IsEssentiallySquareIntegrable.isSquareIntegrable_of_unitaryCentralCharacter`: for
  `0 < n`, a nonzero space `V` (`[Nontrivial V]`) and `ρ` on `V`, if `ρ` is essentially
  square-integrable and has a `UnitaryCentralCharacter`, then `IsSquareIntegrable ρ`.
- `IsEssentiallySquareIntegrable.isSquareIntegrable_of_isUnitarizable`: for `0 < n`, an
  essentially square-integrable `ρ` that is irreducible (`ρ.IsIrreducible`) and unitarizable
  (`IsUnitarizable ρ`, an invariant positive definite Hermitian form, module
  `Langlands.Representation.Unitary.Basic`) is square-integrable modulo the center.

## Proofs

*The uniformizer.* The determinant of the scalar matrix of `ϖ = LocalField.uniformizer F` is
`ϖ^n` (`Matrix.det_diagonal`). By `LocalField.residueNormalizedAbsoluteValue_uniformizer`,
`|ϖ| = q⁻¹`, where `q = LocalField.residueCardinality F > 1`
(`LocalField.residueCardinality_gt_one`). So `|det| = q^{-n} < 1` for `n > 0`.

*Unitary central character.* Write `ρ ⊗ |det|^{-s}` for the square-integrable twist. A Haar
measure on `GL_n(F)/Z` exists (`exists_isHaarMeasure_centralQuotient`), so the definition of
`IsSquareIntegrable` gives a unitary central character of `ρ ⊗ |det|^{-s}`. The given unitary
central character of `ρ` is one of `ρ ⊗ |det|^{-0}` (`realPowerTwist_zero`). On a nonzero
vector, the Library's `Classification.exponent_eq_of_unitaryCentralCharacter` (module
`Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationReduction`)
compares the two at the central element `uniformizerScalarCenter F n`. Their ratio there has
absolute value `|det|^{-s} = q^{ns}`, and both have absolute value one, so `s = 0`. Hence `ρ`
itself is square-integrable.

*Unitarizable representations.* An irreducible representation has a nonzero space
(`IsSimpleModule.nontrivial`). An essentially square-integrable representation is admissible
(`IsEssentiallySquareIntegrable.isAdmissible`). The Library's `unitarizableCentralCharacter`
(module `Langlands.Representation.Unitary.CentralCharacterProof`) gives an irreducible
admissible unitarizable representation a unitary central character. The previous result then
applies.

## Sources

This is the step "ωπ′ est unitaire, et π′ est essentiellement discrète si seulement si c'est
une série discrète" in the proof of the Lemma of Henniart–Lemaire, *Changement de base et
induction automorphe pour GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011), II.4.8,
printed p. 91. There an essentially discrete series is a twist of a discrete series by a
character, and a unitary central character excludes a nontrivial real power of `|det|`. The
Library's `Classification.isSquareIntegrable_of_essential_of_unitaryCentralCharacter` (module
`Langlands.Representation.Classification.SegmentSpecialSquareIntegrabilityCriterionProof`) is
the same argument for the topological data of a `p`-adic field; the present module works
directly over `F`.
