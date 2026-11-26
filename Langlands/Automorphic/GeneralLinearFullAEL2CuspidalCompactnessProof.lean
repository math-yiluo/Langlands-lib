import Langlands.Automorphic.GeneralLinearFullAEL2CuspidalCompactnessStatement
import Langlands.Automorphic.GeneralLinearCuspDisplacement
import Langlands.Automorphic.GroupSchemeQuotientL2ConvolutionOscillation
import Langlands.Automorphic.GroupSchemeFullAEL2ContinuousCuspidality

/-! # Compactness of the actual cuspidal convolutions for `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Filter Topology
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme

namespace Langlands.Automorphic.GroupSchemeFunctions

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3600000 in
/-- Each continuous compact weight acts compactly on the specified full cuspidal Hilbert
space of `GL_n`, with the original positive quotient and full-group Haar measure. -/
theorem generalLinearFullAEL2CuspidalCompactness : GeneralLinearFullAEL2CuspidalCompactnessStatement.{u} := by
  classical
  intro F _ _ n hPD hG T i hi _ I _ e hc _ f hf
  let G := GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
  let : IsAffine G.X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
  let : Smooth G.X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
  let Q := PositiveRationalQuotient F G T i
  let μQ := positiveRationalQuotientHaarMeasure F G T i
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let : T2Space Q := positiveRationalQuotient_t2Space F G T i hi I e hc
  let : BorelSpace Q := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  let R := haarQuotientL2IntegratedAction F G T i hi I e hc μG f hf
  let V := R ∘L S.subtypeL
  have hval (v : S) : V v =
      (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf v).val :=
    (fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc μG f hf v).symm
  suffices hV : IsCompactOperator V by
    have hproj : S.orthogonalProjectionOnto ∘L V =
        fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf := by
      apply ContinuousLinearMap.ext
      intro v
      rw [ContinuousLinearMap.comp_apply, hval]
      exact S.orthogonalProjectionOnto_mem_subspace_eq_self _
    rw [← hproj]
    exact hV.clm_comp S.orthogonalProjectionOnto
  by_cases hn : n = 0
  · subst n
    let A := AdelicGroupPoints F G
    have matrix_subsingleton (B : Type u) [CommRing B] : Subsingleton (GeneralLinear 0 B) :=
      ⟨fun a b => Units.ext (Matrix.ext fun j _ => Fin.elim0 j)⟩
    let : Subsingleton A := ⟨fun a b => (GeneralLinearGroupPoints.adelicHomeomorph F 0).injective
      ((matrix_subsingleton _).elim _ _)⟩
    let : Subsingleton Q :=
      ⟨fun a b => Quotient.inductionOn₂ a b fun x y => congrArg _ (Subsingleton.elim x y)⟩
    let : Finite Q := Finite.of_subsingleton
    let : CompactSpace Q := Finite.compactSpace
    have hu := isCompactOperator_positiveQuotientL2CompactPart F G T i hi I e hc f hf Set.univ
      (isCompact_univ : IsCompact (Set.univ : Set Q)) MeasurableSet.univ
    have hId : quotientL2Indicator (ν := μQ) MeasurableSet.univ = ContinuousLinearMap.id ℂ _ := by
      apply ContinuousLinearMap.ext
      intro v
      apply Lp.ext
      simpa only [Set.indicator_univ, ContinuousLinearMap.id_apply] using
        quotientL2Indicator_ae MeasurableSet.univ v
    change IsCompactOperator (quotientL2Indicator (ν := μQ) MeasurableSet.univ ∘L R) at hu
    rw [hId, ContinuousLinearMap.id_comp] at hu
    exact hu.comp_clm S.subtypeL
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨C, hC, hosc⟩ := exists_positiveQuotientL2ConvolutionOscillation F G T i hi I e hc f hf
    apply isClosed_setOfPred_isCompactOperator.closure_subset
    refine Metric.mem_closure_iff.2 fun δ hδ => ?_
    let ε := δ / (C + 1)
    have hC1 : 0 < C + 1 := by linarith
    have hε : 0 < ε := div_pos hδ hC1
    obtain ⟨U, hU, hUosc⟩ := hosc ε hε
    obtain ⟨D, hD, hDeep⟩ := exists_compact_cuspDisplacementCover F n hPD hG T i hi I e hc hn' U hU
    let M := quotientL2Indicator (ν := μQ) hD.isClosed.measurableSet
    let W := M ∘L V
    have hW : IsCompactOperator W := by
      have h := isCompactOperator_positiveQuotientL2CompactPart F G T i hi I e hc f hf D hD
        hD.isClosed.measurableSet
      exact h.comp_clm S.subtypeL
    have hnorm (v : S) : ‖(V - W) v‖ ≤ (ε * C) * ‖v‖ := by
      obtain ⟨ψ, b, hψ, hb, hosc'⟩ := hUosc v.val
      have hψ' : (V v : Q → ℂ) =ᵐ[μQ] ψ := hψ
      have hcuspidal : positiveQuotientContinuousPullback F G T i ψ ∈
          normalizedParabolicCuspidalSubrepresentation F G hPD hG :=
        (groupSchemeFullAEL2ContinuousCuspidality F G hPD hG T i hi I e hc ψ (V v) hψ').1
          ((hval v).symm ▸ (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf v).property)
      have hWv : (W v : Q → ℂ) =ᵐ[μQ] D.indicator (V v) :=
        quotientL2Indicator_ae hD.isClosed.measurableSet (V v)
      have hdom : ‖V v - W v‖ ≤ ε * ‖b‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [Lp.coeFn_sub (V v) (W v), hψ', hWv, hosc'] with q hsub hq hqW hqosc
        rw [hsub, Pi.sub_apply, hqW]
        by_cases hqD : q ∈ D
        · rw [Set.indicator_of_mem hqD, sub_self, norm_zero]
          exact mul_nonneg hε.le (norm_nonneg _)
        · rw [Set.indicator_of_notMem hqD, sub_zero, hq]
          exact hDeep ψ hcuspidal q hqD _ hqosc
      change ‖V v - W v‖ ≤ _
      exact hdom.trans (by
        simpa only [mul_assoc, Submodule.norm_coe] using mul_le_mul_of_nonneg_left hb hε.le)
    have hop := ContinuousLinearMap.opNorm_le_bound (V - W) (mul_nonneg hε.le hC) hnorm
    have herr : ε * C < δ := by
      calc ε * C < ε * (C + 1) := mul_lt_mul_of_pos_left (by linarith) hε
           _ = δ := div_mul_cancel₀ δ hC1.ne'
    exact ⟨W, hW, by rw [dist_eq_norm]; exact hop.trans_lt herr⟩

end Langlands.Automorphic.GroupSchemeFunctions
