import Langlands.Representation.RankinSelberg.TwoBlockDominantJacquetSeries

/-!
# Ordinary Jacquet realization of every induced coefficient model

Internal coefficient-model assembly using full inverse Whittaker type of the
actual lower induction and its nonzero ordinary Jacquet functional.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩

section Coefficients

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
  (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (hJ0 : J.val ≠ 0)

include hσ hJ0

/-- Every coefficient of any supplied inverse functional is a coefficient of
`J`, including when that supplied functional is zero. -/
theorem exists_section_forInverseCoefficient
    (ell' : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (Z : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) ell').toSubmodule) :
    ∃ f : TwoBlockJacquet.Sections F h σ,
      (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val = Z.val := by
  let ρ := TwoBlockJacquet.inducedRep F h σ
  obtain ⟨c, hc⟩ := (lowerInduced_inverseWhittakerType F h ψ σ hσ).eq_smul hJ0 ell'
  obtain ⟨v, hv⟩ := modelMap_surjective ρ ell' Z
  refine ⟨c • v, ?_⟩
  apply Subtype.ext
  funext g
  change J.val (ρ g (c • v)) = Z.val.val g
  calc
    J.val (ρ g (c • v)) = c * J.val (ρ g v) := by simp only [map_smul, smul_eq_mul]
    _ = ell'.val (ρ g v) := by rw [hc]; rfl
    _ = Z.val.val g := congrArg (fun z => z.val.val g) hv

/-- A section realizing the supplied induced coefficient through `J`.
The choice is algebraic and introduces no convergence assertion. -/
def sectionForInverseCoefficient
    (ell' : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (Z : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) ell').toSubmodule) :
    TwoBlockJacquet.Sections F h σ :=
  Classical.choose (exists_section_forInverseCoefficient F h ψ σ hσ J hJ0 ell' Z)

theorem sectionForInverseCoefficient_spec
    (ell' : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (Z : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) ell').toSubmodule) :
    (modelMap (TwoBlockJacquet.inducedRep F h σ) J
      (sectionForInverseCoefficient F h ψ σ hσ J hJ0 ell' Z)).val = Z.val :=
  Classical.choose_spec (exists_section_forInverseCoefficient F h ψ σ hσ J hJ0 ell' Z)

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
  (hJ : ∀ (f : TwoBlockJacquet.Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier),
    J.val (TwoBlockJacquet.inducedRep F h σ g f) =
      TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g)

include hJ

/-- The chosen section has ordinary Jacquet function equal to the supplied
actual coefficient, for all ambient group elements at once. -/
theorem jacquetFunction_sectionForInverseCoefficient
    (ell' : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (Z : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) ell').toSubmodule)
    (g : GeneralLinear (t + 1) F.Carrier) :
    TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR
      (sectionForInverseCoefficient F h ψ σ hσ J hJ0 ell' Z) g = Z.val.val g := by
  rw [← hJ]
  exact congrArg (fun z => z.val g)
    (sectionForInverseCoefficient_spec F h ψ σ hσ J hJ0 ell' Z)

/-- The actual unfolded series of the chosen section is the equal-rank
coefficient series for the originally supplied inverse-functional model. -/
theorem unfoldedJacquetSeries_sectionForInverseCoefficient [μR.IsAddHaarMeasure]
    (ell' : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (Z : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) ell').toSubmodule)
    (μN : letI := borel (LeftUnipotentQuotient t F.Carrier);
      Measure (LeftUnipotentQuotient t F.Carrier))
    (Wtest : WhittakerFunctions ψ t)
    (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)) :
    unfoldedJacquetSeries F h ψ σ ell μR μN
      (sectionForInverseCoefficient F h ψ σ hσ J hJ0 ell' Z) Wtest Φ =
      equalRankSliceCoefficient F.canonicalTopologicalData μN ψ Wtest Z.val Φ := by
  rw [unfoldedJacquetSeries_eq F h ψ σ ell μR μN J hJ,
    sectionForInverseCoefficient_spec F h ψ σ hσ J hJ0 ell' Z]

end Coefficients

section Family

local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology

/-- One ordinary convergence bound realizes every actual inverse-functional
coefficient model of the deformed lower induction, with no restriction on the
supplied induced functional or coefficient. -/
theorem exists_uniformJacquetCoefficientRealization
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ C : ℝ, ∀ u : ℝ, C < u →
      let σ := twoBlockOppositeTwistBlocks F m τ u
      let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
      (∀ f : TwoBlockJacquet.Sections F h σ,
        TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell0 i).val) μR f) ∧
      ∃ J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ),
        J.val ≠ 0 ∧
        (∀ (f : TwoBlockJacquet.Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier),
          J.val (TwoBlockJacquet.inducedRep F h σ g f) =
            TwoBlockJacquet.jacquetFunction ψ (fun i => (ell0 i).val) μR f g) ∧
        ∀ (ell' : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
          (Z : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) ell').toSubmodule),
          ∃ f : TwoBlockJacquet.Sections F h σ,
            ∀ g : GeneralLinear (t + 1) F.Carrier,
              TwoBlockJacquet.jacquetFunction ψ (fun i => (ell0 i).val) μR f g =
                Z.val.val g := by
  obtain ⟨C, hC⟩ := twoBlockOrdinaryJacquetFunctional p F ψ ν t m h τ hτ ell0 hell0
  refine ⟨C, fun u hu => ?_⟩
  obtain ⟨habs, J, hJ0, hJ⟩ := hC u hu
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro ell' Z
  let σ := twoBlockOppositeTwistBlocks F m τ u
  let ell := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
  have hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i) := fun i =>
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)
  exact ⟨sectionForInverseCoefficient F h ψ σ hσ J hJ0 ell' Z,
    jacquetFunction_sectionForInverseCoefficient F h ψ σ hσ J hJ0 ell μR hJ ell' Z⟩

end Family

end Langlands.RankinSelberg.DominantRankTransport
