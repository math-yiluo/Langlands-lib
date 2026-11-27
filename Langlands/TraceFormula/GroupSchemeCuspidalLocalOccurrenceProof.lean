import Langlands.TraceFormula.GroupSchemeCuspidalLocalOccurrenceStatement
import Langlands.TraceFormula.IsotypicTrace.CuspidalCompactnessOccurrence
import Langlands.Automorphic.GroupSchemeCuspDisplacement
import Langlands.Automorphic.GroupSchemeQuotientL2ConvolutionOscillation

/-! # Local occurrence in every irreducible cuspidal summand -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.TraceFormula

section Compactness

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F G
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "Q" => PositiveRationalQuotient F G T i
local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "μG" => (Measure.haar : Measure (AdelicGroupPoints F G))

/-- Truncating a continuous cuspidal convolution to compact sets converges in operator norm. -/
private theorem isCompactOperator_fullAEL2CuspidalIntegratedAction (f : C_c(A, ℂ))
    (hf : Integrable f μG) : IsCompactOperator
      (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf) := by
  let : T2Space Q := positiveRationalQuotient_t2Space F G T i hi I e hc
  let : BorelSpace Q := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let R := haarQuotientL2IntegratedAction F G T i hi I e hc μG f hf
  let V := R.comp (S).subtypeL
  let Rc := fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf
  have hVapply (v : S) : V v = (Rc v).val :=
    (fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc μG f hf v).symm
  suffices hV : IsCompactOperator V by
    have hproj : (S).orthogonalProjectionOnto.comp V = Rc := by
      apply ContinuousLinearMap.ext
      intro v
      rw [ContinuousLinearMap.comp_apply, hVapply]
      exact (S).orthogonalProjectionOnto_mem_subspace_eq_self _
    change IsCompactOperator Rc
    rw [← hproj]
    exact hV.clm_comp (S).orthogonalProjectionOnto
  obtain ⟨c, hc₀, hosc⟩ := exists_positiveQuotientL2ConvolutionOscillation F G T i hi I e hc f hf
  apply isClosed_setOfPred_isCompactOperator.closure_subset
  refine Metric.mem_closure_iff.2 fun δ hδ => ?_
  let ε := δ / (c + 1)
  have hc₁ : 0 < c + 1 := by linarith
  have hε : 0 < ε := div_pos hδ hc₁
  obtain ⟨U, hU, hUosc⟩ := hosc ε hε
  obtain ⟨D, hD, hDeep⟩ := exists_compact_groupSchemeCuspDisplacementCover
    F G hPD hG T i hi I e hc U hU
  let W := (quotientL2Indicator (ν := μQ) hD.isClosed.measurableSet).comp V
  have hW : IsCompactOperator W := by
    have h := isCompactOperator_positiveQuotientL2CompactPart F G T i hi I e hc f hf D hD
      hD.isClosed.measurableSet
    exact h.comp_clm (S).subtypeL
  have herror (v : S) : ‖(V - W) v‖ ≤ (ε * c) * ‖v‖ := by
    obtain ⟨ψ, b, hψ, hb, hpoint⟩ := hUosc v.val
    have hψ' : (V v : Q → ℂ) =ᵐ[μQ] ψ := hψ
    have hcuspidal : positiveQuotientContinuousPullback F G T i ψ ∈
        normalizedParabolicCuspidalSubrepresentation F G hPD hG :=
      (groupSchemeFullAEL2ContinuousCuspidality F G hPD hG T i hi I e hc ψ (V v) hψ').1
        ((hVapply v).symm ▸ (Rc v).property)
    have hWv : (W v : Q → ℂ) =ᵐ[μQ] D.indicator (V v) :=
      quotientL2Indicator_ae hD.isClosed.measurableSet (V v)
    have hdom : ‖V v - W v‖ ≤ ε * ‖b‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (V v) (W v), hψ', hWv, hpoint] with q hsub hq hqW hqosc
      rw [hsub, Pi.sub_apply, hqW]
      by_cases hqD : q ∈ D
      · rw [Set.indicator_of_mem hqD, sub_self, norm_zero]
        exact mul_nonneg hε.le (norm_nonneg _)
      · rw [Set.indicator_of_notMem hqD, sub_zero, hq]
        exact hDeep ψ hcuspidal q hqD _ hqosc
    change ‖V v - W v‖ ≤ _
    exact hdom.trans (by
      simpa only [mul_assoc, Submodule.norm_coe] using mul_le_mul_of_nonneg_left hb hε.le)
  have hop := ContinuousLinearMap.opNorm_le_bound (V - W) (mul_nonneg hε.le hc₀) herror
  have hlt : ε * c < δ := by
    calc
      ε * c < ε * (c + 1) := mul_lt_mul_of_pos_left (lt_add_one c) hε
      _ = δ := div_mul_cancel₀ δ hc₁.ne'
  exact ⟨W, hW, by rw [dist_eq_norm]; exact hop.trans_lt hlt⟩

end Compactness

/-- Every irreducible cuspidal summand contains a smooth irreducible admissible local
representation at the given finite place. -/
theorem groupSchemeCuspidalLocalOccurrence : GroupSchemeCuspidalLocalOccurrenceStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _ v _ _ _ _ S πc P _ hP0 hPinv _
  exact IsotypicTrace.exists_localOccurrence_of_compactIntegrated F G v πc
    (norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc)
    (fun x => (fullAEL2CuspidalOrbitMap F G hPD hG T i hi I e hc x).continuous)
    (isCompactOperator_fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc) P hP0 hPinv

end Langlands.TraceFormula
