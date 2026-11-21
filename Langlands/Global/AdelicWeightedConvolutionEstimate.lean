import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicRationalConjugateCounting
import Langlands.Global.LeftCosetSupportMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-! # Localized weighted adelic convolution estimate -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped ENNReal Pointwise

namespace Langlands.Global

private theorem restrict_smul_le_withDensity {X : Type u} [MeasurableSpace X]
    (ν : Measure X) {A S : Set X} (hA : MeasurableSet A) (hAS : A ⊆ S)
    {δ : X → ℝ≥0∞} {b : ℝ≥0∞} (hb : ∀ x ∈ A, b ≤ δ x) :
    b • ν.restrict A ≤ (ν.restrict S).withDensity δ := by
  calc
    b • ν.restrict A = (ν.restrict A).withDensity (fun _ => b) :=
      (withDensity_const _).symm
    _ ≤ (ν.restrict A).withDensity δ :=
      withDensity_mono ((ae_restrict_mem hA).mono hb)
    _ ≤ (ν.restrict S).withDensity δ := by
      apply Measure.le_iff.mpr
      intro V hV
      rw [withDensity_apply _ hV, withDensity_apply _ hV]
      exact lintegral_mono' (Measure.restrict_mono_measure (Measure.restrict_mono_set ν hAS) V) le_rfl

section Adelic

open scoped CategoryTheory.MonObj

/-- Control the restriction of the orbital pullback to a compact support by a weighted
measure on a domain containing the translated support. -/
def AdelicWeightedSupportMeasureStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (n : ℕ) (rho : GroupScheme.MatrixRepresentation G (Fin n)),
    0 < n → GroupScheme.IsClosedSubgroup rho →
    (∀ (Γ : Subgroup (AdelicGroupPoints F G))
      (hΓ : Γ ≤ AdelicGroupPoints.rationalSubgroup F G),
      let ν := LeftCosetSpace.haarQuotientMeasure Γ
        ((AdelicGroupPoints.isDiscrete_rationalSubgroup F G).mono hΓ)
      ∃ d : ℕ, ∀ (K : Set (FiniteAdelicGroupPoints F G)), IsCompact K →
        ∀ (C : Set (AdelicGroupPoints F G)), IsCompact C →
          ∃ B : ℝ, 0 ≤ B ∧ ∀ (S : Set (LeftCosetSpace Γ)) (δ : LeftCosetSpace Γ → ℝ≥0∞)
            (x : AdelicGroupPoints F G) (b : ℝ), 0 < b →
            AdelicGroupPoints.finite F G x ∈ K →
            (∀ a ∈ C, LeftCosetSpace.mk Γ (x * a) ∈ S ∧
              ENNReal.ofReal b ≤ δ (LeftCosetSpace.mk Γ (x * a))) →
            Measure.map (fun a => LeftCosetSpace.mk Γ (x * a))
                ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict C) ≤
              ENNReal.ofReal (B * RepresentationGrowth.adelicHeight F G rho x ^ d / b) •
                (ν.restrict S).withDensity δ)

/-- The weight comparison and polynomial orbit count yield the localized measure bound. -/
theorem adelicWeightedSupportMeasure : AdelicWeightedSupportMeasureStatement.{u} := by
  classical
  intro F _ _ G _ _ n rho hn hrho Γ hΓ
  have hΓd : IsDiscrete (Γ : Set (AdelicGroupPoints F G)) :=
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F G).mono hΓ
  let : IsClosed (Γ : Set (AdelicGroupPoints F G)) := Γ.isClosed_of_isDiscrete hΓd
  let : Countable Γ := LeftCosetSpace.countable_of_isDiscrete Γ hΓd
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let ν := LeftCosetSpace.haarQuotientMeasure Γ hΓd
  let q := LeftCosetSpace.mk Γ
  obtain ⟨d, hcount⟩ := adelicRationalConjugateCounting F G n rho hn hrho
  refine ⟨d, fun K hK C hC => ?_⟩
  obtain ⟨B, hB, hcountKC⟩ := hcount K hK (C * C⁻¹) (hC.mul hC.inv)
  refine ⟨B, hB, fun S δ x b hb hx hS => ?_⟩
  let l : AdelicGroupPoints F G ≃ₜ AdelicGroupPoints F G := Homeomorph.mulLeft x
  let A := l '' C
  let E := q '' A
  let D := (fun a => x * a * x⁻¹) '' (C * C⁻¹)
  let R := (AdelicGroupPoints.rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩ D
  obtain ⟨hR, hcard⟩ := hcountKC x hx
  have hD : ∀ a ∈ A, ∀ c ∈ A, a * c⁻¹ ∈ D := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    have hi : c⁻¹ ∈ C⁻¹ := by simpa using hc
    exact ⟨a * c⁻¹, mul_mem_mul ha hi, by simp [l, mul_assoc]⟩
  have hAc := hC.image l.continuous
  have hE : MeasurableSet E := (hAc.image (LeftCosetSpace.continuous_mk Γ)).isClosed.measurableSet
  have hmult : (((Γ : Set (AdelicGroupPoints F G)) ∩ D).encard : ℝ≥0∞) ≤
      ENNReal.ofReal (B * RepresentationGrowth.adelicHeight F G rho x ^ d) := by
    let : Finite (R : Type u) := hR.to_subtype
    have hle := ENat.toENNReal_mono (encard_le_encard (show (Γ : Set _) ∩ D ⊆ R from
      fun _ hy => ⟨hΓ hy.1, hy.2⟩))
    rw [← coe_ncard_eq_encard (s := R), ENat.toENNReal_coe] at hle
    exact hle.trans (by exact_mod_cast ENNReal.ofReal_le_ofReal hcard)
  have hm := LeftCosetSpace.leftCosetSupportMeasure Γ μG
    (LeftCosetSpace.isFundamentalDomain Γ hΓd μG) hAc.isClosed.measurableSet hE
    (show LeftCosetSpace.mk Γ '' A ⊆ E from Subset.rfl) hD
  have htrans : Measure.map (fun a => q (x * a)) (μG.restrict C) =
      Measure.map q (μG.restrict A) := by
    change Measure.map (q ∘ l) (μG.restrict C) = _
    rw [← Measure.map_map (LeftCosetSpace.measurable_mk Γ) l.continuous.measurable]
    congr 1
    calc
      _ = (μG.map l).restrict A := by
        have heq := (l.toMeasurableEquiv.restrict_map μG A).symm
        change Measure.map l (μG.restrict (l ⁻¹' A)) = (μG.map l).restrict A at heq
        rwa [show l ⁻¹' A = C from preimage_image_eq C l.injective] at heq
      _ = μG.restrict A := by
        rw [show μG.map l = μG from map_mul_left_eq_self μG x]
  have hweight (z : LeftCosetSpace Γ) (hz : z ∈ E) :
      z ∈ S ∧ ENNReal.ofReal b ≤ δ z := by
    rcases hz with ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hS a ha
  have hw : ENNReal.ofReal b • ν.restrict E ≤ (ν.restrict S).withDensity δ :=
    restrict_smul_le_withDensity ν hE (fun z hz => (hweight z hz).1)
      (fun z hz => (hweight z hz).2)
  let m := ENNReal.ofReal (B * RepresentationGrowth.adelicHeight F G rho x ^ d)
  have hbn : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.mpr hb).ne'
  change Measure.map (fun a => q (x * a)) (μG.restrict C) ≤
     ENNReal.ofReal (B * RepresentationGrowth.adelicHeight F G rho x ^ d / b) •
        (ν.restrict S).withDensity δ
  rw [htrans, ENNReal.ofReal_div_of_pos hb]
  calc
    _ ≤ (((Γ : Set (AdelicGroupPoints F G)) ∩ D).encard : ℝ≥0∞) • ν.restrict E := hm
    _ ≤ m • ν.restrict E := by
      exact Measure.le_iff.mpr fun V _ => by
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
    _ = (m / ENNReal.ofReal b) • (ENNReal.ofReal b • ν.restrict E) := by
      rw [smul_smul, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hbn ENNReal.ofReal_ne_top,
        mul_one]
    _ ≤ (m / ENNReal.ofReal b) • (ν.restrict S).withDensity δ := by
      exact Measure.le_iff.mpr fun V _ => by
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
        exact Measure.le_iff'.mp hw V

end Adelic

/-- Turn a local pullback measure bound into a convolution estimate by Cauchy–Schwarz. -/
theorem norm_integral_mul_comp_le_of_map_restrict_le {H Q : Type u}
    [MeasurableSpace H] [MeasurableSpace Q] (μ : Measure H) (ν : Measure Q)
    {q : H → Q} (hq : Measurable q) {C : Set H} {B : ℝ} (hB : 0 ≤ B)
    (hdom : Measure.map q (μ.restrict C) ≤ ENNReal.ofReal B • ν)
    {h : H → ℂ} (hh : MemLp h 2 (μ.restrict C)) (hC : Function.support h ⊆ C)
    {f : Q → ℂ} (hf : MemLp f 2 ν) :
    Integrable (fun a => h a * f (q a)) μ ∧
      ‖∫ a, h a * f (q a) ∂μ‖ ≤ ‖hh.toLp h‖ * (Real.sqrt B * ‖hf.toLp f‖) := by
  let μC := μ.restrict C
  let fC := f ∘ q
  have hfM : MemLp f 2 (Measure.map q μC) := hf.of_measure_le_smul ENNReal.ofReal_ne_top hdom
  have hfC : MemLp fC 2 μC := hfM.comp_measurePreserving ⟨hq, rfl⟩
  have hnorm : ‖hfC.toLp fC‖ ≤ Real.sqrt B * ‖hf.toLp f‖ := by
    have hle := eLpNorm_le_of_measure_le_smul hdom (f := f) (p := (2 : ℝ≥0∞))
    rw [eLpNorm_map_measure hfM.aestronglyMeasurable hq.aemeasurable] at hle
    have htop : ENNReal.ofReal B ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm f 2 ν ≠ ∞ :=
      ENNReal.mul_ne_top (by finiteness) hf.eLpNorm_ne_top
    have hr := ENNReal.toReal_mono htop hle
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB] at hr
    have hexp : (1 / (2 : ℝ≥0∞)).toReal = 1 / (2 : ℝ) := by norm_num
    simpa only [hexp, ← Real.sqrt_eq_rpow, Lp.norm_toLp] using hr
  let v := hh.star.toLp (star h)
  let w := hfC.toLp fC
  have hval : (fun a => inner ℂ (v a) (w a)) =ᵐ[μC] fun a => h a * fC a := by
    filter_upwards [hh.star.coeFn_toLp, hfC.coeFn_toLp] with a ha hw
    change v a = star (h a) at ha
    change w a = fC a at hw
    simp [ha, hw, mul_comm]
  have hi : Integrable (fun a => h a * fC a) μC := (L2.integrable_inner v w).congr hval
  have hzero : ∀ a ∉ C, h a * fC a = 0 := fun a ha => by
    have hha : h a = 0 := by
      by_contra hne
      exact ha (hC hne)
    rw [hha, zero_mul]
  refine ⟨(integrableOn_iff_integrable_of_support_subset (fun a ha =>
    not_imp_comm.mp (hzero a) ha)).mp hi, ?_⟩
  change ‖∫ a, h a * fC a ∂μ‖ ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) hzero]
  calc
    _ = ‖inner ℂ v w‖ := by rw [L2.inner_def, integral_congr_ae hval]
    _ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm v w
    _ ≤ ‖hh.toLp h‖ * (Real.sqrt B * ‖hf.toLp f‖) := by
      have hv : ‖v‖ = ‖hh.toLp h‖ := by rw [Lp.norm_toLp, eLpNorm_star, Lp.norm_toLp]
      rw [hv]
      exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

end Langlands.Global
