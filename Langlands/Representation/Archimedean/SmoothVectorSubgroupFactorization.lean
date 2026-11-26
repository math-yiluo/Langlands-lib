import Langlands.Representation.Archimedean.SmoothVectorLineFactorization
import Langlands.Analysis.DixmierMalliavin.IteratedKernel
import Langlands.Geometry.Manifold.LinearLieGroup.HaarDensity

/-! # Smooth-vector factorization along a linear Lie subgroup -/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Archimedean.DerivativeSmoothVectors

open Langlands.LinearLieGroup
open Langlands.Analysis.DixmierMalliavin (contDiff_cons_kernel tsupport_cons_kernel)

universe uA uE

section DirectionalProducts

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E))
  {G : Subgroup Aˣ} {𝔤 : Submodule ℝ A} (h : IsExpLieAlgebra G 𝔤)

local notation "I" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors I R

private def inverseCoefficient (L : D →L[ℂ] ℂ) (v : D) (x : G) : ℂ :=
  L (representation I R ((x⁻¹ : G) : Aˣ) v)

omit [CompleteSpace E] in
private theorem continuous_inverseCoefficient (hR : IsContinuousRepresentation R) (L : D →L[ℂ] ℂ) (v : D) :
    Continuous (inverseCoefficient R (G := G) L v) :=
  L.continuous.comp ((continuous_representation_units R hR).comp
    ((continuous_subtype_val.comp continuous_inv).prodMk continuous_const))

include h in
private theorem inverseCoefficient_factor_direction (hR : IsContinuousRepresentation R) (X : 𝔤) (v : D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : D) (a b : ℝ → ℂ), ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      tsupport a ⊆ Icc (-ε) ε ∧ tsupport b ⊆ Icc (-ε) ε ∧
      ∀ (L : D →L[ℂ] ℂ) (x : G),
        inverseCoefficient R L v x =
          (∫ s, a s * inverseCoefficient R L w (h.expG (s • X) * x)) +
            ∫ s, b s * inverseCoefficient R L v (h.expG (s • X) * x) := by
  obtain ⟨w, a, b, ha, hb, has, hbs, hEq⟩ :=
    smoothVectorLineFactorization R hR (-(X : A)) v ε hε
  have hs : Icc (0 : ℝ) ε ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) le_rfl
  refine ⟨w, a, b, ha, hb, has.trans hs, hbs.trans hs, fun L x => ?_⟩
  let Lx := L.comp (SmoothAction.derivativeAction I R ((x⁻¹ : G) : Aˣ))
  have hArg (u : D) (s : ℝ) : Lx (smoothExponentialOrbit R (-(X : A)) u s) =
      inverseCoefficient R L u (h.expG (s • X) * x) := by
    change L (representation I R ((x⁻¹ : G) : Aˣ)
      (representation I R (expUnit A (s • -(X : A))) u)) = _
    rw [← Module.End.mul_apply, ← map_mul, inverseCoefficient, mul_inv_rev, Subgroup.coe_mul,
      ← h.expG_neg]
    simp only [IsExpLieAlgebra.expG, Submodule.coe_neg, Submodule.coe_smul, smul_neg]
  have hEq' := hEq Lx
  simp_rw [hArg] at hEq'
  exact hEq'

private theorem exists_finite_inverseCoefficient (hR : IsContinuousRepresentation R) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ {d : ℕ} (X : Fin d → 𝔤) (v : D),
      ∃ (m : ℕ) (w : Fin m → D) (K : Fin m → (Fin d → ℝ) → ℂ),
        (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ closedBall 0 ε) ∧
        ∀ (L : D →L[ℂ] ℂ) (x : G), inverseCoefficient R L v x =
          ∑ i, ∫ t, K i t * inverseCoefficient R L (w i) (h.revProdExp X t * x) := by
  intro d
  induction d with
  | zero =>
    intro X v
    refine ⟨1, fun _ => v, fun _ _ => 1, fun _ => ⟨contDiff_const, ?_⟩, ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]
      exact mem_closedBall_self hε.le
    · intro L x
      simp only [Fin.sum_univ_one, h.revProdExp_zero, one_mul, integral_const]
      have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      rw [hv, one_smul]
  | succ d ih =>
    intro X v
    obtain ⟨w, a, b, ha, hb, has, hbs, hLine⟩ := inverseCoefficient_factor_direction R h hR (X 0) v hε
    obtain ⟨m₁, w₁, K₁, hK₁, h₁⟩ := ih (Fin.tail X) w
    obtain ⟨m₂, w₂, K₂, hK₂, h₂⟩ := ih (Fin.tail X) v
    refine ⟨m₁ + m₂, Fin.append w₁ w₂,
      Fin.append (fun i t => a (t 0) * K₁ i (Fin.tail t)) (fun i t => b (t 0) * K₂ i (Fin.tail t)),
      ?_, fun L x => ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using And.intro (contDiff_cons_kernel ha (hK₁ i).1)
          (tsupport_cons_kernel hε.le has (hK₁ i).2)
      · simpa only [Fin.append_right] using And.intro (contDiff_cons_kernel hb (hK₂ i).1)
          (tsupport_cons_kernel hε.le hbs (hK₂ i).2)
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hLine L x]
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le ha.continuous has (fun i => (hK₁ i).1.continuous)
          (fun i => (hK₁ i).2) (fun i => continuous_inverseCoefficient R hR L (w₁ i)) (h₁ L) x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hb.continuous hbs (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => continuous_inverseCoefficient R hR L (w₂ i)) (h₂ L) x).symm

end DirectionalProducts

/-- Smooth-vector factorization for the restriction of a continuous Banach
representation of the ambient units to a linear Lie subgroup. -/
def SmoothVectorSubgroupFactorizationStatement : Prop :=
  ∀ (A : Type uA) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : Aˣ →* (E →L[ℂ] E)) (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A) (h : IsExpLieAlgebra G 𝔤)
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    let model := 𝓘(ℝ, A)
    let D := DerivativeSmoothVectors model R
    IsContinuousRepresentation R →
    ∀ (U : Set G), U ∈ 𝓝 (1 : G) → ∀ (v : D),
      ∃ (m : ℕ) (w : Fin m → D) (K : Fin m → G → ℂ),
        (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (K i)) ∧
          HasCompactSupport (K i) ∧ tsupport (K i) ⊆ U) ∧
        ∀ L : D →L[ℂ] ℂ,
          L v = ∑ i, ∫ x, K i x * L (representation model R (x : Aˣ) (w i)) ∂μ

theorem smoothVectorSubgroupFactorization : SmoothVectorSubgroupFactorizationStatement.{uA, uE} := by
  intro A _ _ _ _ E _ _ _ R G 𝔤 h _ _ μ _ model D hR U hU v
  classical
  let b := Module.finBasis ℝ 𝔤
  obtain ⟨ε₀, hε₀, hdens⟩ := h.exists_smooth_density_prodExp μ b
  have hP0 : h.prodExp (⇑b) 0 = 1 := Subtype.ext (Units.ext (by rw [h.val_prodExp, prodExpVal_zero]; rfl))
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    ((h.continuous_prodExp (⇑b)).continuousAt.preimage_mem_nhds (t := U) (x := 0) (by rwa [hP0]))
  let ε := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  obtain ⟨m, w, K, hK, hEq⟩ := exists_finite_inverseCoefficient R h hR hε (⇑b) v
  have hK' (i : Fin m) : ContDiff ℝ ∞ (fun t => K i (-t)) ∧
      tsupport (fun t => K i (-t)) ⊆ closedBall 0 ε := by
    refine ⟨(hK i).1.comp contDiff_neg, fun t ht => ?_⟩
    have ht' : -t ∈ tsupport (K i) :=
      tsupport_comp_subset_preimage (K i) (f := fun t => -t) continuous_neg ht
    have hnorm := (hK i).2 ht'
    simpa only [mem_closedBall_zero_iff, norm_neg] using hnorm
  choose κ hκs hκc hκV hκ using fun i => hdens ε (min_le_left _ _) (fun t => K i (-t)) (hK' i).1 (hK' i).2
  refine ⟨m, w, κ, fun i => ⟨hκs i, hκc i,
    (hκV i).trans (image_subset_iff.2 ((closedBall_subset_closedBall (min_le_right _ _)).trans hball))⟩,
    fun L => ?_⟩
  have hBase := hEq L 1
  simp only [inverseCoefficient, mul_one, inv_one, OneMemClass.coe_one, map_one,
    Module.End.one_apply] at hBase
  rw [hBase]
  refine Finset.sum_congr rfl fun i _ => ?_
  let φ : G → ℂ := fun x => L (representation model R (x : Aˣ) (w i))
  have hφ : Continuous φ := L.continuous.comp
    ((continuous_representation_units R hR).comp (continuous_subtype_val.prodMk continuous_const))
  change _ = ∫ x, κ i x * φ x ∂μ
  rw [hκ i φ hφ]
  have ht (t : Fin (Module.finrank ℝ 𝔤) → ℝ) :
      K i (-t) * φ (h.prodExp (⇑b) t) =
        (fun s => K i s * φ (h.revProdExp (⇑b) s)⁻¹) (-t) := by
    have hh := h.revProdExp_inv (⇑b) (-t)
    rw [neg_neg] at hh
    simp only [← hh]
  simp_rw [ht]
  exact (integral_neg_eq_self (fun s => K i s * φ (h.revProdExp (⇑b) s)⁻¹) volume).symm

end Langlands.Archimedean.DerivativeSmoothVectors
