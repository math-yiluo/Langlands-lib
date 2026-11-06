import Langlands.Automorphic.GroupSchemeParabolicL2ClosednessStatement
import Langlands.Analysis.Local.NormalizedCompactPeriodL2Proof
import Langlands.Analysis.Local.QuotientPeriodAEEqProof

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.QuotientIntegration

/-- Actual all-proper canonical periods on the full positive quotient L2 space. -/
theorem groupSchemeParabolicL2Closedness : GroupSchemeParabolicL2ClosednessStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _
  let Γ := rationalNormOneSubgroup F G
  have hd : IsDiscrete (Γ : Set (normOneSubgroup F G)) :=
    isDiscrete_rationalNormOneSubgroup F G
  have hcl : IsClosed (Γ : Set (normOneSubgroup F G)) := Γ.isClosed_of_isDiscrete hd
  let : Countable Γ := LeftCosetSpace.countable_of_isDiscrete Γ hd
  let : IsFiniteMeasureOnCompacts (Measure.count : Measure Γ) :=
    LeftCosetSpace.isFiniteMeasureOnCompacts_count Γ hd
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let ambientMeasure : Measure (normOneSubgroup F G) := Measure.haar
  let : ambientMeasure.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  have hν : IsCompatible Γ ambientMeasure.inv.inv Measure.count
      (normOneRationalQuotientHaarMeasure F G) := by
    simpa only [Measure.inv_inv] using normOneRationalQuotientHaarMeasure_isCompatible F G
  let mp := measurePreserving_positiveQuotient F G T i hi I e hc
  let pull : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i) →ₗᵢ[ℂ]
      Lp ℂ 2 (normOneRationalQuotientHaarMeasure F G) :=
    Lp.compMeasurePreservingₗᵢ ℂ (positiveQuotientMeasurableEquiv F G T i hi I e hc) mp
  have hP (P : ProperRationalParabolic G) :
      (∀ φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i),
        (∀ᵐ g ∂ambientMeasure, HasConvergentProperParabolicPositivePeriod F G hPD hG T i P φ g) ∧
        LocallyIntegrable (properParabolicPositivePeriod F G hPD hG T i P φ) ambientMeasure) ∧
      (∀ f : C_c(normOneSubgroup F G, ℂ),
        ∃ ℓ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i) →L[ℂ] ℂ,
          ∀ φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i),
            Integrable (fun g => star (f g) *
            properParabolicPositivePeriod F G hPD hG T i P φ g) ambientMeasure ∧
            ℓ φ = ∫ g, star (f g) *
              properParabolicPositivePeriod F G hPD hG T i P φ g ∂ambientMeasure) ∧
      IsClosed {φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i) |
        properParabolicPositivePeriod F G hPD hG T i P φ =ᵐ[ambientMeasure] 0} := by
    let U := properRationalParabolicRadicals hPD hG P
    let Λ := AdelicSubgroupPoints.rationalSubgroup F G U
    let hΛ := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G U
    let j := (properParabolicNormOneInclusion F G hPD hG P).toMonoidHom
    let hjΛ := properParabolicNormOneInclusion_rational_mem F G hPD hG P
    let radicalMeasure : Measure (AdelicSubgroupPoints.adelicPoints F G U) := Measure.haar
    obtain ⟨K, hK, hcover⟩ := LeftCosetSpace.exists_isCompact_cover Λ
    have hcover' : ∀ h, ∃ n : Λ, (n : AdelicSubgroupPoints.adelicPoints F G U) * h ∈ K := by
      intro h
      obtain ⟨n, hn, hnh⟩ := hcover h
      exact ⟨⟨n, hn⟩, hnh⟩
    have hn := normalizedCompactPeriodL2 ambientMeasure.inv Γ hcl Measure.count
      (normOneRationalQuotientHaarMeasure F G) hν Λ hΛ radicalMeasure (NeZero.ne _)
      K hK hcover' j (properParabolicNormOneInclusion F G hPD hG P).continuous hjΛ
      1 continuous_const (fun _ => rfl)
    simp only [Measure.inv_inv] at hn
    let P₀ := normalizedQuotientCharacterPeriod Γ Λ j hjΛ 1 (fun _ => rfl) hΛ radicalMeasure
    have hcompare (φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) :
        ∀ᵐ g ∂ambientMeasure,
          (HasConvergentQuotientCharacterPeriod Γ Λ j hjΛ 1 (fun _ => rfl)
            (LeftCosetSpace.normalizedMeasure Λ radicalMeasure (LeftCosetSpace.fundamentalDomain Λ hΛ))
            (pull φ) g ↔
            HasConvergentProperParabolicPositivePeriod F G hPD hG T i P φ g) ∧
          P₀ (pull φ) g = properParabolicPositivePeriod F G hPD hG T i P φ g := by
      let ψ : NormOneRationalQuotient F G → ℂ :=
        fun q => φ (normOneToPositiveQuotient F G T i q)
      have hψ : StronglyMeasurable ψ :=
        (Lp.stronglyMeasurable φ).comp_measurable mp.measurable
      have heq : (pull φ : NormOneRationalQuotient F G → ℂ) =ᵐ[
          LeftCosetSpace.discreteQuotientMeasure Γ hd ambientMeasure] ψ :=
        Lp.coeFn_compMeasurePreserving φ mp
      have he := quotientPeriodAEEq Γ hd ambientMeasure Λ hΛ radicalMeasure j
        (properParabolicNormOneInclusion F G hPD hG P).continuous hjΛ
        1 continuous_const (fun _ => rfl) (pull φ) ψ (Lp.stronglyMeasurable _) hψ heq
      filter_upwards [he] with g hg
      have hcvg := hg.2.1
      have hval := hg.2.2
      have hmass := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_eq_normalizedMeasure
        F G U
      have hcvg' : HasConvergentQuotientCharacterPeriod Γ Λ j hjΛ 1 (fun _ => rfl)
          (LeftCosetSpace.normalizedMeasure Λ radicalMeasure (LeftCosetSpace.fundamentalDomain Λ hΛ))
          (pull φ) g ↔
          HasConvergentProperParabolicPositivePeriod F G hPD hG T i P φ g := by
        change _ ↔ Integrable _ (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U)
        rw [hmass]
        exact hcvg
      refine ⟨hcvg', ?_⟩
      rw [properParabolicPositivePeriod_eq_normalizedPeriod]
      exact hval
    have hperiod (φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) :
        P₀ (pull φ) =ᵐ[ambientMeasure] properParabolicPositivePeriod F G hPD hG T i P φ :=
      (hcompare φ).mono fun _ hg => hg.2
    refine ⟨?_, ?_, ?_⟩
    · intro φ
      obtain ⟨hcvg, hlocal⟩ := hn.1 (pull φ)
      refine ⟨?_, hlocal.congr (hperiod φ)⟩
      filter_upwards [hcvg, hcompare φ] with g hg hc
      exact hc.1.mp hg
    · intro f
      obtain ⟨ℓ, hℓ⟩ := hn.2.1 f
      refine ⟨ℓ.comp pull.toContinuousLinearMap, ?_⟩
      intro φ
      obtain ⟨hint, heq⟩ := hℓ (pull φ)
      have heqtest : (fun g => star (f g) * P₀ (pull φ) g) =ᵐ[ambientMeasure]
          fun g => star (f g) * properParabolicPositivePeriod F G hPD hG T i P φ g := by
        filter_upwards [hperiod φ] with g hg
        rw [hg]
      exact ⟨hint.congr heqtest, heq.trans (integral_congr_ae heqtest)⟩
    · have hs := hn.2.2.preimage pull.continuous
      convert hs using 1
      ext φ
      change (properParabolicPositivePeriod F G hPD hG T i P φ =ᵐ[ambientMeasure] 0) ↔
        P₀ (pull φ) =ᵐ[ambientMeasure] 0
      exact ⟨fun h => (hperiod φ).trans h, fun h => (hperiod φ).symm.trans h⟩
  refine ⟨fun P φ => (hP P).1 φ, fun P f => (hP P).2.1 f, ?_⟩
  have hset : fullAEL2CuspidalLocus F G hPD hG T i =
      ⋂ P : ProperRationalParabolic G,
        {φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i) |
          properParabolicPositivePeriod F G hPD hG T i P φ =ᵐ[ambientMeasure] 0} := by
    ext φ
    change (∀ P, (∀ᵐ g ∂ambientMeasure,
      HasConvergentProperParabolicPositivePeriod F G hPD hG T i P φ g) ∧
      properParabolicPositivePeriod F G hPD hG T i P φ =ᵐ[ambientMeasure] 0) ↔ _
    simp only [mem_iInter, mem_ofPred_eq]
    exact ⟨fun h P => (h P).2, fun h P => ⟨((hP P).1 φ).1, h P⟩⟩
  rw [hset]
  exact isClosed_iInter fun P => (hP P).2.2

end Langlands.Automorphic.GroupSchemeFunctions
