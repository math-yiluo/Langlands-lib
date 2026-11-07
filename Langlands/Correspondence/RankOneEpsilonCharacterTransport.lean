import Langlands.Correspondence.RankOneArithmeticEpsilon
import Langlands.LocalField.CanonicalTransport

/-! # Bottom-field characters in the rank-one arithmetic epsilon formula -/

noncomputable section

universe uF uP uV

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance baseCharacterTransportTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance baseCharacterTransportBottomTopology :
    TopologicalSpace (baseExtension F).field :=
  (fieldData F (baseExtension F)).topology

/-- The existing bottom-field equivalence respects the specified p-adic base. -/
def baseFieldPadicEquiv :
    letI := ((baseExtension F).asPadicField (p := p)).algebra
    (baseExtension F).field ≃ₐ[Padic p] F.Carrier := by
  letI := ((baseExtension F).asPadicField (p := p)).algebra
  refine
    { (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).toRingEquiv with
      commutes' := ?_ }
  intro a
  change IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)
    (algebraMap F.Carrier (baseExtension F).field (algebraMap (Padic p) F.Carrier a)) =
      algebraMap (Padic p) F.Carrier a
  exact (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).commutes _

/-- On actual units, the bottom-field equivalence is a topological group equivalence. -/
def baseFieldUnitsEquiv : (baseExtension F).fieldˣ ≃ₜ* F.Carrierˣ := by
  letI := ((baseExtension F).asPadicField (p := p)).algebra
  letI := ((baseExtension F).asPadicField (p := p)).canonicalNormedField
  letI := F.canonicalNormedField
  exact
    { toMulEquiv := Units.mapEquiv (baseFieldPadicEquiv F).toMulEquiv
      continuous_toFun := (Weil.Local.extension_isometry
        ((baseExtension F).asPadicField (p := p)) F
        (baseFieldPadicEquiv F).toAlgHom).continuous.units_map _
      continuous_invFun := (Weil.Local.extension_isometry F
        ((baseExtension F).asPadicField (p := p))
        (baseFieldPadicEquiv F).symm.toAlgHom).continuous.units_map _ }

@[simp]
theorem baseFieldUnitsEquiv_apply (a : (baseExtension F).fieldˣ) :
    (baseFieldUnitsEquiv F a : F.Carrier) =
      IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)
        (a : (baseExtension F).field) := rfl

/-- Actual quasicharacter transport through the canonical bottom-field equivalence. -/
def baseFieldCharacterEquiv : QuasiCharacter F ≃ FieldCharacter F (baseExtension F) :=
  LocalClassField.characterTransport (baseFieldUnitsEquiv F).symm

@[simp]
theorem baseFieldCharacterEquiv_apply (χ : QuasiCharacter F)
    (a : (baseExtension F).fieldˣ) :
    baseFieldCharacterEquiv F χ a = χ (baseFieldUnitsEquiv F a) := rfl

@[simp]
theorem baseFieldCharacterEquiv_mul (χ η : QuasiCharacter F) :
    baseFieldCharacterEquiv F (χ * η) =
      baseFieldCharacterEquiv F χ * baseFieldCharacterEquiv F η := rfl

/-- The explicit compatibility condition identifies the two actual units. -/
theorem IsBaseReciprocity.units_eq {e : ReciprocityCandidate F} {eC : ReciprocityFamily F}
    (h : IsBaseReciprocity F e eC) (w : weilSubgroup F (baseExtension F)) :
    baseFieldUnitsEquiv F (reciprocityUnits F eC (baseExtension F) w) =
      RankOne.reciprocityUnits F e w.val := by
  apply Units.ext
  exact h w

/-- Compatible reciprocity pulls the transported field character back to the
restriction of its standalone Weil character. -/
theorem weilCharacter_baseFieldCharacterEquiv
    {e : ReciprocityCandidate F} {eC : ReciprocityFamily F}
    (h : IsBaseReciprocity F e eC) (χ : QuasiCharacter F) :
    CommonClosure.weilCharacter F eC (baseExtension F) (baseFieldCharacterEquiv F χ) =
      baseRestrictedWeilCharacter F (RankOne.weilCharacter F e χ) := by
  apply ContinuousMonoidHom.ext
  intro w
  change χ (baseFieldUnitsEquiv F (reciprocityUnits F eC (baseExtension F) w)) =
    χ (RankOne.reciprocityUnits F e w.val)
  rw [h.units_eq F]

/-- Descent of the restricted standalone Weil character recovers exactly the
transported original quasicharacter. -/
theorem fieldCharacterEquiv_baseRestrictedWeilCharacter
    {e : ReciprocityCandidate F} {eC : ReciprocityFamily F}
    (h : IsBaseReciprocity F e eC) (χ : QuasiCharacter F) :
    CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC (baseExtension F)
        (baseRestrictedWeilCharacter F (RankOne.weilCharacter F e χ)) =
      baseFieldCharacterEquiv F χ := by
  rw [← weilCharacter_baseFieldCharacterEquiv F h χ, fieldCharacterEquiv_weilCharacter]

/-- Descent preserves the actual pointwise character product. -/
theorem fieldCharacterEquiv_mul (eC : ReciprocityFamily F) (E : Extension F)
    (χ η : weilSubgroup F E →ₜ* ℂˣ) :
    CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC E (χ * η) =
      CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC E χ * CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC E η := by
  apply (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC E).symm.injective
  change CommonClosure.weilCharacter F eC E
      (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC E (χ * η)) =
    CommonClosure.weilCharacter F eC E
      (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC E χ * CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC E η)
  rw [CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]
  change χ * η =
    CommonClosure.weilCharacter F eC E (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC E χ) *
      CommonClosure.weilCharacter F eC E (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC E η)
  rw [CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv, CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]

/-- Compatible base reciprocity separates the descended spectral character from
the transported product of the original field quasicharacters. -/
theorem fieldCharacterEquiv_rankOneSpectralProduct
    {e : ReciprocityCandidate F} {eC : ReciprocityFamily F}
    (h : IsBaseReciprocity F e eC) (χ η : QuasiCharacter F) (s : ℂ) :
    CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC (baseExtension F)
      (CommonClosureSpectral.character F (baseExtension F) s *
        (baseRestrictedWeilCharacter F (RankOne.weilCharacter F e χ) *
          baseRestrictedWeilCharacter F (RankOne.weilCharacter F e η))) =
      CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC (baseExtension F)
          (CommonClosureSpectral.character F (baseExtension F) s) *
        baseFieldCharacterEquiv F (χ * η) := by
  rw [fieldCharacterEquiv_mul, fieldCharacterEquiv_mul,
    fieldCharacterEquiv_baseRestrictedWeilCharacter F h χ,
    fieldCharacterEquiv_baseRestrictedWeilCharacter F h η,
    baseFieldCharacterEquiv_mul]

/-- Compatible reciprocity expresses the full arithmetic pair epsilon value
using the transported product of the original field quasicharacters. -/
theorem conditionalPairEpsilonValue_of_compatible_rankOneBaseRestriction
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (χ η : QuasiCharacter F)
    (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    {A B : Pair.{uF, uV} F (baseExtension F)}
    (hA : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ)) A)
    (hB : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) B)
    (hAc : A.toFiniteRepresentation.IsContinuous) (hBc : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F (baseExtension F)) (s : ℂ) :
    (CommonClosureGamma.conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ
      A B hAc hBc Φ s : ℂ) =
      (fieldData F (baseExtension F)).abelianEpsilonExpression
        (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC (baseExtension F)
            (CommonClosureSpectral.character F (baseExtension F) s) *
          baseFieldCharacterEquiv F (χ * η)) ψ' μ := by
  rw [conditionalPairEpsilonValue_of_rankOneBaseRestriction
    F e eC ε hε χ η ψ' μ hA hB hAc hBc Φ s,
    fieldCharacterEquiv_rankOneSpectralProduct F h χ η s]

/-- The full arithmetic certificate retains all harmonic existence and
universal clauses after rewriting the original field-character product. -/
theorem isArithmeticPairEpsilonFactor_compatible_rankOneWeilCharacterClass_iff
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (χ η : QuasiCharacter F) (c : ℂˣ) (m : ℤ) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ))
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) c m ↔
      (∃ (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F)),
        IsBaseCharacter F ψ ψ' ∧ CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ) ∧
      Nonempty (GeometricFrobenius F (baseExtension F)) ∧
      ∀ (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F)),
        IsBaseCharacter F ψ ψ' →
        CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ →
        ∀ s : ℂ,
          (fieldData F (baseExtension F)).abelianEpsilonExpression
            (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC (baseExtension F)
                (CommonClosureSpectral.character F (baseExtension F) s) *
              baseFieldCharacterEquiv F (χ * η)) ψ' μ =
            RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality c m s := by
  rw [isArithmeticPairEpsilonFactor_rankOneWeilCharacterClass_iff
    F e eC ε hε ψ χ η c m]
  simp_rw [fieldCharacterEquiv_rankOneSpectralProduct F h χ η]

end Langlands.Correspondence
