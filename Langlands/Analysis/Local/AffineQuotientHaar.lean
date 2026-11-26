import Langlands.Analysis.Local.CompactOpenQuotientChart
import Langlands.Analysis.Local.StrictDerivativeBallChart
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Group.Units

/-! # Quotient Haar measure in affine transverse coordinates -/

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure Metric Set _root_.Topology Langlands.QuotientIntegration
open scoped NNReal

universe u v w z

variable {F : Type u} [NontriviallyNormedField F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R]
  {S : Type w} [NormedAddCommGroup S] [NormedSpace F S]
  {W : Type z} [NormedAddCommGroup W] [NormedSpace F W]

/-- Subtracting the identity from the value of a unit gives its affine coordinate. -/
def unitAffine (g : Rˣ) : R := g.val - 1

@[simp]
theorem unitAffine_one : unitAffine (1 : Rˣ) = 0 := sub_self _

theorem isOpenEmbedding_unitAffine [CompleteSpace R] : IsOpenEmbedding (unitAffine : Rˣ → R) :=
  (Homeomorph.subRight (1 : R)).isOpenEmbedding.comp Units.isOpenEmbedding_val

/-- The centered product of the affine torus and transverse coordinates. -/
def affineFactorization (e : (S × W) ≃L[F] R) (x : S × W) : R :=
  (1 + e (x.1, 0)) * (1 + e (0, x.2)) - 1

@[simp]
theorem affineFactorization_zero (e : (S × W) ≃L[F] R) : affineFactorization e 0 = 0 := by
  simp [affineFactorization, show ((0, 0) : S × W) = 0 from rfl]

theorem hasStrictFDerivAt_affineFactorization (e : (S × W) ≃L[F] R) :
    HasStrictFDerivAt (affineFactorization e) (e : S × W →L[F] R) 0 := by
  let i := (e : S × W →L[F] R).comp
    ((ContinuousLinearMap.inl F S W).comp (ContinuousLinearMap.fst F S W))
  let j := (e : S × W →L[F] R).comp
    ((ContinuousLinearMap.inr F S W).comp (ContinuousLinearMap.snd F S W))
  have hi := i.hasStrictFDerivAt (x := 0) |>.const_add (c := (1 : R))
  have hj := j.hasStrictFDerivAt (x := 0) |>.const_add (c := (1 : R))
  have hd : (1 + i 0) • j + MulOpposite.op (1 + j 0) • i = (e : S × W →L[F] R) := by
    simp only [map_zero, add_zero, MulOpposite.op_one, one_smul]
    apply ContinuousLinearMap.ext
    intro x
    change e (0, x.2) + e (x.1, 0) = e x
    rw [← map_add, show (0, x.2) + (x.1, 0) = x by ext <;> simp]
  rw [← hd]
  exact (hi.mul' hj).sub_const 1

/-- A subgroup unit belongs to the ambient coordinate ball exactly when
its subgroup coordinate belongs to the corresponding smaller ball. -/
theorem comap_unitAffine_ball [CompleteSpace R] (e : (S × W) ≃L[F] R)
    (H : Subgroup Rˣ) (a : H → S) (haG : ∀ h : H, unitAffine h.val = e (a h, 0))
    (K : OpenSubgroup Rˣ) {r : ℝ} (hr : 0 ≤ r)
    (hKr : unitAffine '' (K : Set Rˣ) = e '' closedBall 0 r) :
    (K.comap H.subtype continuous_subtype_val : Set H) = a ⁻¹' closedBall 0 r := by
  have hB : closedBall (0 : S) r ×ˢ closedBall (0 : W) r = closedBall 0 r :=
    closedBall_prod_same 0 0 r
  ext h
  change h.val ∈ (K : Set Rˣ) ↔ a h ∈ closedBall 0 r
  constructor
  · intro hh
    have hv : unitAffine h.val ∈ unitAffine '' (K : Set Rˣ) := mem_image_of_mem _ hh
    rw [hKr, haG, ← hB] at hv
    obtain ⟨x, hx, heq⟩ := hv
    rw [e.injective heq] at hx
    exact hx.1
  · intro hh
    have hv : unitAffine h.val ∈ unitAffine '' (K : Set Rˣ) := by
      rw [hKr, haG, ← hB]
      exact mem_image_of_mem _ ⟨hh, mem_closedBall_self hr⟩
    obtain ⟨k, hk, hkh⟩ := hv
    exact isOpenEmbedding_unitAffine.injective hkh ▸ hk

section Haar

variable [CompleteSpace R] [SecondCountableTopology R] [LocallyCompactSpace R]
  [SecondCountableTopology W] [ProperSpace W]
  [MeasurableSpace R] [BorelSpace R] [MeasurableSpace Rˣ] [BorelSpace Rˣ]
  [MeasurableSpace S] [BorelSpace S] [MeasurableSpace W] [BorelSpace W]

/-- Product Haar coordinates in a compact open subgroup of units give an
exact Haar coordinate on the corresponding compatible quotient orbit. -/
theorem affineQuotientChart (e : (S × W) ≃L[F] R)
    (H : Subgroup Rˣ) (hH : IsClosed (H : Set Rˣ))
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μG : Measure Rˣ) [μG.IsHaarMeasure] [μG.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular] [μH.IsMulRightInvariant]
    (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μG μH ν)
    (a : H → S) (ha : IsOpenEmbedding a) (ha1 : a 1 = 0)
    (haG : ∀ h : H, unitAffine h.val = e (a h, 0))
    (ξS : Measure S) [SFinite ξS] (ξW : Measure W)
    [SFinite ξW] [IsFiniteMeasureOnCompacts ξW]
    (K : OpenSubgroup Rˣ) (hK : IsCompact (K : Set Rˣ))
    (cG cS : ℝ≥0) (hcS : 0 < cS) {r : ℝ} (hr : 0 < r)
    (hKr : unitAffine '' (K : Set Rˣ) = e '' closedBall 0 r)
    (haS : closedBall (0 : S) r ⊆ range a)
    (hμG : (μG.restrict (K : Set Rˣ)).map unitAffine =
      cG • ((ξS.prod ξW).map e).restrict (e '' closedBall 0 r))
    (hμH : (μH.restrict (K.comap H.subtype continuous_subtype_val : Set H)).map a =
      cS • ξS.restrict (closedBall 0 r))
    (hφ : IsOpenEmbedding (fun x : closedBall (0 : S × W) r => affineFactorization e x.val))
    (hφr : affineFactorization e '' closedBall 0 r = e '' closedBall 0 r)
    (hφμ : ((ξS.prod ξW).restrict (closedBall 0 r)).map (affineFactorization e) =
      ((ξS.prod ξW).map e).restrict (e '' closedBall 0 r)) :
    ∃ s : closedBall (0 : W) r → K,
      (∀ x, (s x : Rˣ).val = 1 + e (0, x.val)) ∧
      let c := fun x => leftQuotientMap H (s x : Rˣ)
      IsOpenEmbedding c ∧ c ⟨0, mem_closedBall_self hr.le⟩ = leftQuotientMap H 1 ∧
        ((cG / cS) • ξW.comap Subtype.val).map c = ν.restrict (range c) := by
  let A := K.comap H.subtype continuous_subtype_val
  let BS := closedBall (0 : S) r
  let BW := closedBall (0 : W) r
  let B := closedBall (0 : S × W) r
  have hB : BS ×ˢ BW = B := closedBall_prod_same 0 0 r
  change unitAffine '' (K : Set Rˣ) = e '' B at hKr
  have hA : (A : Set H) = a ⁻¹' BS := comap_unitAffine_ball e H a haG K hr.le hKr
  have hA' : range (a ∘ (Subtype.val : A → H)) = BS := by
    rw [range_comp, Subtype.range_coe, hA, image_preimage_eq_of_subset haS]
  let AS : A ≃ₜ BS := (ha.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr hA')
  let K' := isOpenEmbedding_unitAffine.isEmbedding.homeomorphImage (K : Set Rˣ)
  let φ' : B ≃ₜ unitAffine '' (K : Set Rˣ) := hφ.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by rw [hKr]; exact (Set.range_domRestrict _ B).trans hφr))
  let p : BS × BW ≃ₜ B := (Homeomorph.Set.prod BS BW).symm.trans (Homeomorph.setCongr hB)
  let m : A × BW ≃ₜ K := ((AS.prodCongr (Homeomorph.refl BW)).trans p).trans (φ'.trans K'.symm)
  have hm (x : A × BW) : unitAffine (m x).val = affineFactorization e (a x.1.val, x.2.val) := by
    have h := congrArg Subtype.val (K'.apply_symm_apply (φ' (p (AS x.1, x.2))))
    exact h
  let s : BW → K := fun w => m (1, w)
  have hs (x : BW) : (s x : Rˣ).val = 1 + e (0, x.val) := by
    have h := hm (1, x)
    change (s x : Rˣ).val - 1 = _ at h
    rw [show ((1 : A).val : H) = 1 from rfl, ha1] at h
    apply eq_add_of_sub_eq'
    simpa [affineFactorization, show ((0, 0) : S × W) = 0 from rfl] using h
  have hmm (x : A × BW) : (m x : Rˣ) = (x.1.val : Rˣ) * (s x.2 : Rˣ) := by
    apply isOpenEmbedding_unitAffine.injective
    rw [hm, affineFactorization, unitAffine, Units.val_mul, hs]
    have h := haG x.1.val
    change ((x.1.val : H) : Rˣ).val - 1 = _ at h
    rw [eq_add_of_sub_eq' h]
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let : SecondCountableTopology Rˣ := isOpenEmbedding_unitAffine.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace Rˣ := isOpenEmbedding_unitAffine.locallyCompactSpace
  let d := cG / cS
  let ξW' : Measure BW := d • ξW.comap Subtype.val
  have hBW : MeasurableSet BW := isClosed_closedBall.measurableSet
  have hBWe : MeasurableEmbedding (Subtype.val : BW → W) := .subtype_coe hBW
  let : IsFiniteMeasure (ξW.comap (Subtype.val : BW → W)) := ⟨by
    rw [hBWe.comap_apply, image_univ, Subtype.range_coe]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hAe : MeasurableEmbedding (Subtype.val : A → H) :=
    A.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hmapA : (μH.comap (Subtype.val : A → H)).map (a ∘ Subtype.val) =
      cS • ξS.restrict BS := by
    rw [← Measure.map_map ha.continuous.measurable hAe.measurable, hAe.map_comap]
    rw [Subtype.range_coe, hμH]
  have hmapW : ξW'.map (Subtype.val : BW → W) = d • ξW.restrict BW := by
    rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable,
      (MeasurableEmbedding.subtype_coe hBW).map_comap, Subtype.range_coe]
  have hmap : ((μH.comap (Subtype.val : A → H)).prod ξW').map
      (fun x : A × BW => (a x.1.val, x.2.val)) = cG • (ξS.prod ξW).restrict B := by
    rw [show (fun x : A × BW => (a x.1.val, x.2.val)) =
      Prod.map (a ∘ Subtype.val) Subtype.val from rfl,
      ← Measure.map_prod_map _ _ (ha.continuous.measurable.comp hAe.measurable) measurable_subtype_coe,
      hmapA, hmapW, Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.prod_restrict, hB, smul_smul, mul_div_cancel₀ _ hcS.ne']
  let f : A × BW → Rˣ := fun x => (m x : Rˣ)
  have hf : Measurable f := (continuous_subtype_val.comp m.continuous).measurable
  have hf' : Measurable (affineFactorization e) := by
    unfold affineFactorization
    fun_prop
  have hprod : ((μH.comap A.subtype).prod ξW').map f = μG.restrict (K : Set Rˣ) := by
    apply isOpenEmbedding_unitAffine.measurableEmbedding.map_injective
    rw [Measure.map_map isOpenEmbedding_unitAffine.continuous.measurable hf, hμG]
    change ((μH.comap (Subtype.val : A → H)).prod ξW').map (unitAffine ∘ f) = _
    have hcomp : unitAffine ∘ f =
        affineFactorization e ∘ (fun x : A × BW => (a x.1.val, x.2.val)) := funext hm
    rw [hcomp]
    have hcoord : Measurable (fun x : A × BW => (a x.1.val, x.2.val)) :=
      (ha.continuous.measurable.comp (hAe.measurable.comp measurable_fst)).prodMk
        (measurable_subtype_coe.comp measurable_snd)
    rw [← Measure.map_map hf' hcoord, hmap,
      Measure.map_smul _ hf'.aemeasurable, hφμ]
  obtain ⟨hc, _, hμ⟩ := compactOpenQuotientChart H hH μG μH ν hν K hK ξW' s m hmm hprod
  refine ⟨s, hs, hc, ?_, hμ⟩
  apply congrArg (leftQuotientMap H)
  apply Units.ext
  simp [hs, show ((0, 0) : S × W) = 0 from rfl]

end Haar
end Langlands.Analysis
