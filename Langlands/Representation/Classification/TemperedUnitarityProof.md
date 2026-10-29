# Unitarity of irreducible analytically tempered GL_n representations

This module proves the published closed proposition
`Langlands.GLTemperedUnitarityStatement.{uF,uV}`
(`Langlands.Representation.Classification.TemperedInductionStatement`) as
the theorem `Langlands.glTemperedUnitarity`: for every prime `p`,
`F : PadicField.{uF} p`, `T : F.TopologicalData`, positive rank `n`, carrier
`V : Type uV` with its supplied module structure, and representation `ρ` of
`GL_n(F)` on `V`, if `ρ` is irreducible and `T.IsTempered ρ`, then `ρ` is
unitarizable, i.e. `V` carries an actual `ρ`-invariant positive definite
Hermitian form.

The theorem is `glTemperedUnitarity_of` applied to three published closed
theorems, imported by Lean name, and adds no hypothesis:

- `Langlands.glTemperedDiscreteSeriesSupport.{uF,uV}`
  (`Langlands.Representation.Classification.TemperedSupportProof`), which
  proves `GLTemperedDiscreteSeriesSupportStatement.{uF,uV}`: the
  representation embeds into the normalized opposite parabolic induction of
  an irreducible representation of a product Levi that is square-integrable
  modulo the center for every Borel Haar measure;
- `Langlands.squareIntegrableUnimodularUnitarity`
  (`Langlands.Representation.Unitary.SquareIntegrableProof`), the generic
  square-integrable unitarity theorem;
- `Langlands.glNormalizedParabolicInductionUnitarity`
  (`Langlands.Representation.Induction.UnitaryProof`), unitarity of upper
  normalized parabolic induction of smooth unitarizable representations.

## Source

Silberger, *Introduction to harmonic analysis on reductive p-adic groups*
(1979), registered as `silberger-1979-harmonic-analysis`, Corollary 4.5.13
(printed p. 190, one-based PDF p. 196): an irreducible admissible tempered
representation is unitary. The printed proof is "Apply Corollary 1.7.9 and
Corollary 4.5.11". Corollary 4.5.11 (pp. 189-190) embeds a tempered
representation into a representation induced from a discrete series of a
Levi subgroup; Corollary 1.7.9 (printed p. 46, PDF p. 52) says that
induction from a cocompact subgroup of a smooth unitary representation is
unitary and smooth. The Lean proof follows the same two steps, with the
analytic support supplied by the published support theorem, unitarity of
the square-integrable Levi representation supplied by the generic
square-integrable theorem, and the induction step reduced from opposite
to upper parabolic induction by inverse transpose.

## Declarations

- The imported `InvariantPositiveForm.comp` and `IsUnitarizable.comp` from
  `Langlands.Representation.Unitary.Restriction`: an invariant
  positive form for `ρ` is an invariant positive form for `ρ.comp φ`, for
  any monoid homomorphism `φ`.
- `isMulRightInvariant_of_positiveCharacter_eq_one`: on a locally compact
  group whose `ℝ≥0`-valued characters are all trivial, every regular Haar
  measure is right invariant. The proof writes the right translate of the
  measure as a scalar multiple of the measure
  (`Measure.isMulLeftInvariant_eq_smul_of_regular`), identifies the scalar
  with Mathlib's `Measure.modularCharacter`, and uses that this character
  is trivial. It is the argument of the published
  `GeneralLinear.haar_centralQuotient_isMulRightInvariant`
  (`Langlands.Group.GL.CentralQuotientMeasure`), stated for an arbitrary
  group so that it applies to the product Levi.
- `GeneralLinear.BlockShape.mulSingle_scalar_mem_center`: a scalar matrix
  placed in one block is central in the product Levi.
- The imported `GeneralLinear.BlockShape.leviCentralQuotient_positiveCharacter_eq_one`
  from `Langlands.Group.GL.LeviCentralQuotientMeasure` states that every `ℝ≥0`-valued character of the full central quotient of the product
  Levi is trivial. Its pullback to the Levi is determined by its
  restrictions to the blocks (`MonoidHom.pi_ext`); each restriction is a
  character of one general linear group that is trivial on scalars, hence
  trivial by the published
  `RankinSelberg.GeneralLinearUnimodularity.character_eq_one`.
- `GeneralLinear.BlockShape.leviInverseTranspose` (with its `_apply`
  lemma): blockwise inverse transpose of the product Levi.
- `GeneralLinear.BlockShape.leviInverseTranspose_leviProjection_oppositeToUpper`:
  blockwise inverse transpose of the upper Levi projection of
  `oppositeToUpperInverseTranspose q` is the opposite Levi projection of
  `q`, by the published `leviProjection_oppositeToUpperInverseTranspose`
  and involutivity of inverse transpose.
- `PadicField.TopologicalData.leviCentralQuotientHaar_rightInvariant`:
  every Borel Haar measure on the full central quotient of an actual product
  Levi is right invariant. Local compactness and Hausdorffness come from the
  published `glBlockCentralQuotientTopology`; regularity is automatic for
  Haar measures on second countable locally compact groups.
- `PadicField.TopologicalData.leviCompactOpen_cofinal`: compact open
  subgroups are cofinal among open subgroups of the product Levi, from the
  published `leviCompactOpen`.
- `PadicField.TopologicalData.leviSquareIntegrable_smooth_unitarizable`:
  an irreducible product-Levi
  representation that is square-integrable modulo the center for every
  Borel Haar measure is smooth and unitarizable. It chooses the Borel
  structure on the quotient and a Haar measure there
  (`exists_isHaarMeasure_leviCentralQuotient`); smoothness is part of
  `IsSquareIntegrableModCenter` (through admissibility); the published
  `squareIntegrableUnimodularUnitarity.{uF,uV}` is applied with the two
  lemmas above.
- `PadicField.TopologicalData.isUnitarizable_normalizedOppositeParabolicInduced`:
  normalized opposite parabolic induction of a smooth unitarizable Levi representation `σ` is
  unitarizable. Let `σ' = σ ∘ leviInverseTranspose`; it is smooth
  (`isSmooth_comp`, continuity of blockwise inverse transpose) and
  unitarizable (`IsUnitarizable.comp`). The published upper theorem
  `glNormalizedParabolicInductionUnitarity` makes
  `normalizedParabolicInduced B σ'` unitarizable, hence also its pullback
  along ambient inverse transpose. The published
  `Induction.precomposeSmoothInducedEquiv` identifies this pullback with
  `normalizedOppositeParabolicInduced B σ`: the needed twist identity uses
  `parabolicHalfModulus_oppositeToUpperInverseTranspose` and the Levi
  projection lemma above. `isUnitarizable_iff_of_equiv` transports the form.
- `glTemperedUnitarity_of`: by the support statement (taken as its only
  argument), an irreducible tempered `ρ` admits a block shape, an irreducible square-integrable Levi
  representation `σ` and an injective intertwiner `j` into
  `normalizedOppositeParabolicInduced B σ`; the induced representation is
  unitarizable by the previous two declarations, and
  `IsUnitarizable.of_injective` pulls the form back along `j`.
- `glTemperedUnitarity`: the target theorem, `glTemperedUnitarity_of`
  applied to the published `glTemperedDiscreteSeriesSupport.{uF,uV}`.

## Acyclicity

The module does not use `GLLeviTemperedUnitarityStatement`,
`GLTemperedInductionStatement`, `GLTemperedInductionPrerequisitesStatement`,
tempered exhaustion, square-integrable block induction or the Langlands
classification.
