import Langlands.Representation.Archimedean.SmoothVectorLineFactorization
import Langlands.Analysis.DixmierMalliavin.IteratedKernel
import Langlands.Geometry.Manifold.LinearLieGroup.HaarDensity
import Langlands.Geometry.Manifold.LinearLieGroup.Units

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

universe uA uB uE

section DirectionalProducts

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]
  {B : Type uB} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [FiniteDimensional ℝ B]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Bˣ →* (E →L[ℂ] E))
  {G : Subgroup Aˣ} {𝔤 : Submodule ℝ A} (h : IsExpLieAlgebra G 𝔤)
  (σ : G →* Bˣ) (j : 𝔤 →ₗ[ℝ] B)

local notation "I" => 𝓘(ℝ, B)
local notation "D" => DerivativeSmoothVectors I R

private def inverseCoefficient (L : D →L[ℂ] ℂ) (v : D) (x : G) : ℂ :=
  L (representation I R (σ x⁻¹) v)

omit [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A] [CompleteSpace E] in
private theorem continuous_inverseCoefficient (hR : IsContinuousRepresentation R)
    (hσ : Continuous σ) (L : D →L[ℂ] ℂ) (v : D) :
    Continuous (inverseCoefficient R σ (G := G) L v) :=
  L.continuous.comp ((continuous_representation_units R hR).comp
    ((hσ.comp continuous_inv).prodMk continuous_const))

omit [FiniteDimensional ℝ A] in
private theorem inverseCoefficient_factor_direction (hR : IsContinuousRepresentation R)
    (hExp : ∀ (t : ℝ) (Y : 𝔤), σ (h.expG (t • Y)) = expUnit B (t • j Y))
    (X : 𝔤) (v : D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : D) (a b : ℝ → ℂ), ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      tsupport a ⊆ Icc (-ε) ε ∧ tsupport b ⊆ Icc (-ε) ε ∧
      ∀ (L : D →L[ℂ] ℂ) (x : G),
        inverseCoefficient R σ L v x =
          (∫ s, a s * inverseCoefficient R σ L w (h.expG (s • X) * x)) +
            ∫ s, b s * inverseCoefficient R σ L v (h.expG (s • X) * x) := by
  obtain ⟨w, a, b, ha, hb, has, hbs, hEq⟩ :=
    smoothVectorLineFactorization R hR (-(j X)) v ε hε
  have hs : Icc (0 : ℝ) ε ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) le_rfl
  refine ⟨w, a, b, ha, hb, has.trans hs, hbs.trans hs, fun L x => ?_⟩
  let Lx := L.comp (SmoothAction.derivativeAction I R (σ x⁻¹))
  have hArg (u : D) (s : ℝ) : Lx (smoothExponentialOrbit R (-(j X)) u s) =
      inverseCoefficient R σ L u (h.expG (s • X) * x) := by
    change L (representation I R (σ x⁻¹)
      (representation I R (expUnit B (s • -(j X))) u)) = _
    rw [← Module.End.mul_apply, ← map_mul, inverseCoefficient]
    have hg : σ x⁻¹ * expUnit B (s • -(j X)) = σ ((h.expG (s • X) * x)⁻¹) := by
      rw [mul_inv_rev, map_mul σ, ← h.expG_neg, ← neg_smul, hExp, neg_smul, smul_neg]
    rw [hg]
  have hEq' := hEq Lx
  simp_rw [hArg] at hEq'
  exact hEq'

omit [FiniteDimensional ℝ A] in
private theorem exists_finite_inverseCoefficient (hR : IsContinuousRepresentation R)
    (hσ : Continuous σ) (hExp : ∀ (t : ℝ) (Y : 𝔤), σ (h.expG (t • Y)) = expUnit B (t • j Y))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ {d : ℕ} (X : Fin d → 𝔤) (v : D),
      ∃ (m : ℕ) (w : Fin m → D) (K : Fin m → (Fin d → ℝ) → ℂ),
        (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ closedBall 0 ε) ∧
        ∀ (L : D →L[ℂ] ℂ) (x : G), inverseCoefficient R σ L v x =
          ∑ i, ∫ t, K i t * inverseCoefficient R σ L (w i) (h.revProdExp X t * x) := by
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
    obtain ⟨w, a, b, ha, hb, has, hbs, hLine⟩ := inverseCoefficient_factor_direction R h σ j hR hExp (X 0) v hε
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
          (fun i => (hK₁ i).2) (fun i => continuous_inverseCoefficient R σ hR hσ L (w₁ i)) (h₁ L) x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hb.continuous hbs (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => continuous_inverseCoefficient R σ hR hσ L (w₂ i)) (h₂ L) x).symm

end DirectionalProducts

section CommutingDirections

variable {B : Type uB} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

private theorem val_revProdExp_eq_exp_sum {d : ℕ} (Y : Fin d → (⊤ : Submodule ℝ B))
    (hY : ∀ i j, Commute (Y i : B) (Y j : B)) (t : Fin d → ℝ) :
    ((isExpLieAlgebra_top.revProdExp Y t : Bˣ) : B) = NormedSpace.exp (∑ i, t i • (Y i : B)) := by
  induction d with
  | zero => simp [isExpLieAlgebra_top.revProdExp_zero, NormedSpace.exp_zero]
  | succ d ih =>
    rw [isExpLieAlgebra_top.revProdExp_succ]
    change ((isExpLieAlgebra_top.revProdExp (Fin.tail Y) (Fin.tail t) : Bˣ) : B) *
      NormedSpace.exp (t 0 • (Y 0 : B)) = _
    rw [ih (Fin.tail Y) (fun i j => hY i.succ j.succ), Fin.sum_univ_succ]
    have hc : Commute (t 0 • (Y 0 : B)) (∑ i : Fin d, t i.succ • (Y i.succ : B)) :=
      Commute.sum_right _ _ _ fun i _ => ((hY 0 i.succ).smul_left _).smul_right _
    exact (exp_add_of_commute' hc.symm).symm.trans (congrArg NormedSpace.exp (add_comm _ _))

/-- A genuine smooth vector admits finite compact smooth averaging along any finite family of
commuting real Lie directions, with Lebesgue measure in the supplied coordinates. -/
def SmoothVectorCommutingDirectionsFactorizationStatement : Prop :=
  ∀ (B : Type uB) [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [FiniteDimensional ℝ B]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : Bˣ →* (E →L[ℂ] E)),
    let I := 𝓘(ℝ, B)
    let D := DerivativeSmoothVectors I R
    IsContinuousRepresentation R → ∀ (d : ℕ) (X : (Fin d → ℝ) →ₗ[ℝ] B),
      (∀ t u, Commute (X t) (X u)) → ∀ v : D,
      ∃ (m : ℕ) (w : Fin m → D) (K : Fin m → (Fin d → ℝ) → ℂ),
        (∀ i, ContDiff ℝ ∞ (K i) ∧ HasCompactSupport (K i)) ∧
        ∀ L : D →L[ℂ] ℂ,
          L v = ∑ i, ∫ t, K i t * L (representation I R (expUnit B (X t)) (w i))

theorem smoothVectorCommutingDirectionsFactorization :
    SmoothVectorCommutingDirectionsFactorizationStatement.{uB, uE} := by
  intro B _ _ _ _ E _ _ _ R I D hR d X hX v
  let G : Subgroup Bˣ := ⊤
  let 𝔤 : Submodule ℝ B := ⊤
  let h : IsExpLieAlgebra G 𝔤 := isExpLieAlgebra_top
  let Y (i : Fin d) : 𝔤 := ⟨-X (Pi.single i 1), Submodule.mem_top⟩
  obtain ⟨m, w, K, hK, hEq⟩ := exists_finite_inverseCoefficient R h G.subtype 𝔤.subtype hR
    continuous_subtype_val (fun _ _ => rfl) (show (0 : ℝ) < 1 by norm_num) Y v
  refine ⟨m, w, K, fun i => ⟨(hK i).1, (isCompact_closedBall 0 1).of_isClosed_subset
    (isClosed_tsupport _) (hK i).2⟩, fun L => ?_⟩
  have hsum (t : Fin d → ℝ) : ∑ i, t i • (Y i : B) = -X t := by
    have ht := congrArg (fun z => X z) (pi_eq_sum_univ' t)
    simp only [map_sum, map_smul] at ht
    simp only [Y, smul_neg, Finset.sum_neg_distrib, ← ht]
  have hY (i j : Fin d) : Commute (Y i : B) (Y j : B) := ((hX _ _).neg_left).neg_right
  have hArg (t : Fin d → ℝ) : ((h.revProdExp Y t)⁻¹ : Bˣ) = expUnit B (X t) := by
    have hVal : (h.revProdExp Y t : Bˣ) = expUnit B (-X t) := by
      apply Units.ext
      rw [val_revProdExp_eq_exp_sum Y hY t, hsum, coe_expUnit]
    change (h.revProdExp Y t : Bˣ)⁻¹ = _
    rw [hVal]
    apply Units.ext
    rw [coe_expUnit_inv, neg_neg, coe_expUnit]
  simpa only [inverseCoefficient, Subgroup.coe_mul, Subgroup.coe_one, Subgroup.coe_inv, map_one,
    mul_one, inv_one, Module.End.one_apply, Subgroup.subtype_apply, hArg] using hEq L 1

end CommutingDirections

/-- Smooth-vector factorization along a continuous group map taking subgroup exponential lines
into ambient exponential lines with the specified Lie directions. -/
def SmoothVectorMappedSubgroupFactorizationStatement : Prop :=
  ∀ (A : Type uA) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    (B : Type uB) [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [FiniteDimensional ℝ B]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : Bˣ →* (E →L[ℂ] E)) (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A) (h : IsExpLieAlgebra G 𝔤)
    (σ : G →* Bˣ) (j : 𝔤 →ₗ[ℝ] B)
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    let model := 𝓘(ℝ, B)
    let D := DerivativeSmoothVectors model R
    IsContinuousRepresentation R → Continuous σ →
    (∀ (t : ℝ) (Y : 𝔤), σ (h.expG (t • Y)) = expUnit B (t • j Y)) →
    ∀ (U : Set G), U ∈ 𝓝 (1 : G) → ∀ (v : D),
      ∃ (m : ℕ) (w : Fin m → D) (K : Fin m → G → ℂ),
        (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (K i)) ∧
          HasCompactSupport (K i) ∧ tsupport (K i) ⊆ U) ∧
        ∀ L : D →L[ℂ] ℂ,
          L v = ∑ i, ∫ x, K i x * L (representation model R (σ x) (w i)) ∂μ

theorem smoothVectorMappedSubgroupFactorization :
    SmoothVectorMappedSubgroupFactorizationStatement.{uA, uB, uE} := by
  intro A _ _ _ _ B _ _ _ _ E _ _ _ R G 𝔤 h σ j _ _ μ _ model D hR hσ hExp U hU v
  classical
  let b := Module.finBasis ℝ 𝔤
  obtain ⟨ε₀, hε₀, hdens⟩ := h.exists_smooth_density_prodExp μ b
  have hP0 : h.prodExp (⇑b) 0 = 1 := Subtype.ext (Units.ext (by rw [h.val_prodExp, prodExpVal_zero]; rfl))
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    ((h.continuous_prodExp (⇑b)).continuousAt.preimage_mem_nhds (t := U) (x := 0) (by rwa [hP0]))
  let ε := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  obtain ⟨m, w, K, hK, hEq⟩ := exists_finite_inverseCoefficient R h σ j hR hσ hExp hε (⇑b) v
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
  simp only [inverseCoefficient, mul_one, inv_one, map_one, Module.End.one_apply] at hBase
  rw [hBase]
  refine Finset.sum_congr rfl fun i _ => ?_
  let φ : G → ℂ := fun x => L (representation model R (σ x) (w i))
  have hφ : Continuous φ := L.continuous.comp
    ((continuous_representation_units R hR).comp (hσ.prodMk continuous_const))
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
  exact smoothVectorMappedSubgroupFactorization A A E R G 𝔤 h G.subtype 𝔤.subtype μ hR
    continuous_subtype_val (fun _ _ => rfl) U hU v

end Langlands.Archimedean.DerivativeSmoothVectors
