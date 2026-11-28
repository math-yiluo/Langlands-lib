import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialProductStraighteningStatement
import Langlands.HarmonicAnalysis.UnitConjugation.SmallExponentialConjugators
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.NoncommRing

/-! # Isometric straightening of products in small exponential coordinates -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Metric Set Function _root_.Topology
open scoped NNReal

section Displacement

variable {A : Type*} [NormedRing A] [IsUltrametricDist A]

private theorem norm_sub_le_max_norm (x y : A) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa only [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

private def commutator (a x : A) : A := a * x - x * a

private theorem norm_commutator_le (a x : A) : ‖commutator a x‖ ≤ ‖a‖ * ‖x‖ := by
  apply (norm_sub_le_max_norm (a * x) (x * a)).trans
  apply max_le (norm_mul_le _ _)
  simpa only [mul_comm ‖x‖ ‖a‖] using norm_mul_le x a

omit [IsUltrametricDist A] in
private theorem conj_sub_eq (u : Aˣ) (x : A) :
    conjugationHomeomorph u x - x = commutator ((u : A) - 1) x * (↑u⁻¹ : A) := by
  rw [conjugationHomeomorph_apply]
  calc
    _ = ((u : A) * x - x * (u : A)) * (↑u⁻¹ : A) := by
      rw [sub_mul, mul_assoc x (u : A), Units.mul_inv, mul_one]
    _ = _ := by
      unfold commutator
      congr 1
      noncomm_ring

private theorem norm_displacement_sub_le {u v : Aˣ} {x y : A} {c r d : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hd : 0 ≤ d) (hcr : c * r ≤ 1)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hxy : ‖x - y‖ ≤ d)
    (hv : ‖(v : A) - 1‖ ≤ c * r)
    (huv : ‖(u : A) - (v : A)‖ ≤ c * d)
    (hInv : ‖(↑u⁻¹ : A)‖ ≤ max 1 ‖(1 : A)‖) (hInvDiff : ‖(↑u⁻¹ : A) - (↑v⁻¹ : A)‖ ≤ c * d) :
    ‖(conjugationHomeomorph u x - x) - (conjugationHomeomorph v y - y)‖ ≤
      (max 1 ‖(1 : A)‖ * c * r) * d := by
  let K := max (1 : ℝ) ‖(1 : A)‖
  let a := (u : A) - 1
  let b := (v : A) - 1
  have hK : 1 ≤ K := le_max_left _ _
  have hPos : 0 ≤ c * r := mul_nonneg hc hr
  have hDiff : ‖a - b‖ ≤ c * d := by simpa only [a, b, sub_sub_sub_cancel_right] using huv
  have hComm : ‖commutator a x - commutator b y‖ ≤ c * r * d := by
    have hEq : commutator a x - commutator b y = commutator (a - b) x + commutator b (x - y) := by
      unfold commutator
      noncomm_ring
    rw [hEq]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · exact (norm_commutator_le _ _).trans ((mul_le_mul hDiff hx (norm_nonneg _) (mul_nonneg hc hd)).trans_eq (by ring))
    · exact (norm_commutator_le _ _).trans (mul_le_mul hv hxy (norm_nonneg _) hPos)
  have hCommY : ‖commutator b y‖ ≤ c * r * r :=
    (norm_commutator_le _ _).trans (mul_le_mul hv hy (norm_nonneg _) hPos)
  rw [conj_sub_eq u, conj_sub_eq v]
  change ‖commutator a x * (↑u⁻¹ : A) - commutator b y * (↑v⁻¹ : A)‖ ≤ _
  have hEq : commutator a x * (↑u⁻¹ : A) - commutator b y * (↑v⁻¹ : A) =
      (commutator a x - commutator b y) * (↑u⁻¹ : A) + commutator b y * ((↑u⁻¹ : A) - (↑v⁻¹ : A)) := by
    rw [sub_mul, mul_sub]
    abel
  rw [hEq]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · exact (norm_mul_le _ _).trans ((mul_le_mul hComm hInv (norm_nonneg _) (mul_nonneg hPos hd)).trans_eq (by ring))
  · calc
      _ ≤ ‖commutator b y‖ * ‖(↑u⁻¹ : A) - (↑v⁻¹ : A)‖ := norm_mul_le _ _
      _ ≤ (c * r * r) * (c * d) := mul_le_mul hCommY hInvDiff (norm_nonneg _) (mul_nonneg hPos hr)
      _ = (c * r * d) * (c * r) := by ring
      _ ≤ (K * c * r) * d := by
        rw [show K * c * r * d = (c * r * d) * K by ring]
        exact mul_le_mul_of_nonneg_left (hcr.trans hK) (mul_nonneg hPos hd)

end Displacement

section BallIsometry

variable {P : Type*} [NormedAddCommGroup P] [IsUltrametricDist P] [CompleteSpace P]

private theorem exists_isometryEquiv_ball_add {r : ℝ} (hr : 0 ≤ r)
    (δ : closedBall (0 : P) r → P) (hzero : δ ⟨0, mem_closedBall_self hr⟩ = 0)
    {c : ℝ≥0} (hc : c < 1)
    (hδ : ∀ x y, ‖δ x - δ y‖ ≤ (c : ℝ) * ‖(x : P) - (y : P)‖) :
    ∃ e : closedBall (0 : P) r ≃ᵢ closedBall (0 : P) r, ∀ x, (e x : P) = x.val + δ x := by
  let B := closedBall (0 : P) r
  let o : B := ⟨0, mem_closedBall_self hr⟩
  have hNorm (x : B) : ‖x.val‖ ≤ r := dist_zero_right x.val ▸ x.property
  have hclt : (c : ℝ) < 1 := by exact_mod_cast hc
  have hDisp (x : B) : ‖δ x‖ ≤ r := by
    have h := hδ x o
    rw [show δ o = 0 from hzero, show o.val = 0 from rfl, sub_zero, sub_zero] at h
    exact h.trans ((mul_le_of_le_one_left (norm_nonneg _) hclt.le).trans (hNorm x))
  let f (x : B) : B := ⟨x.val + δ x, by
    rw [mem_closedBall, dist_zero_right]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hNorm x) (hDisp x))⟩
  have hIso : Isometry f := Isometry.of_dist_eq fun x y => by
    by_cases hxy : x = y
    · simp [hxy]
    have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    have hlt := (hδ x y).trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hclt)
    change dist (x.val + δ x) (y.val + δ y) = dist x.val y.val
    rw [dist_eq_norm, dist_eq_norm, show x.val + δ x - (y.val + δ y) = (δ x - δ y) + (x.val - y.val) by abel,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]
  have hSurj : Surjective f := by
    intro y
    let g (x : B) : B := ⟨y.val - δ x, by
      rw [mem_closedBall, dist_zero_right, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hNorm y) (by simpa only [norm_neg] using hDisp x))⟩
    have hg : ContractingWith c g := ⟨hc, LipschitzWith.of_dist_le_mul fun x z => by
      change dist (y.val - δ x) (y.val - δ z) ≤ (c : ℝ) * dist x.val z.val
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev]
      exact hδ x z⟩
    let : CompleteSpace B := (isClosed_closedBall : IsClosed B).isComplete.completeSpace_coe
    obtain ⟨x, hx, _, _⟩ := hg.exists_fixedPoint o (edist_ne_top _ _)
    refine ⟨x, Subtype.ext ?_⟩
    change x.val + δ x = y.val
    have hx' : y.val - δ x = x.val := congrArg Subtype.val hx
    exact (eq_add_of_sub_eq hx').symm
  exact ⟨{ Equiv.ofBijective f ⟨hIso.injective, hSurj⟩ with isometry_toFun := hIso }, fun _ => rfl⟩

end BallIsometry

section Product

variable {A : Type*} [NormedRing A] [IsUltrametricDist A]

private theorem pairIsUltrametric : IsUltrametricDist (A × A) := by
  constructor
  intro x y z
  simp only [Prod.dist_eq]
  apply max_le
  · exact (IsUltrametricDist.dist_triangle_max x.1 y.1 z.1).trans
      (max_le_max (le_max_left _ _) (le_max_left _ _))
  · exact (IsUltrametricDist.dist_triangle_max x.2 y.2 z.2).trans
      (max_le_max (le_max_right _ _) (le_max_right _ _))

omit [IsUltrametricDist A] in
private theorem mem_pairBall {p : A × A} {r : ℝ} :
    p ∈ closedBall (0 : A × A) r ↔ p.1 ∈ closedBall (0 : A) r ∧ p.2 ∈ closedBall (0 : A) r := by
  simp only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]

private def pairBallIsometry (r : ℝ) : closedBall (0 : A × A) r ≃ᵢ
    (closedBall (0 : A) r × closedBall (0 : A) r) where
  toFun p := (⟨p.val.1, (mem_pairBall.mp p.property).1⟩, ⟨p.val.2, (mem_pairBall.mp p.property).2⟩)
  invFun p := ⟨(p.1.val, p.2.val), mem_pairBall.mpr ⟨p.1.property, p.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl

end Product

variable (F A : Type*) [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
  [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [CompleteSpace A]

/-- The quantitative conjugator estimates imply the exponential product
straightening statement with isometric bijections on the small balls. -/
def ExponentialStraighteningFromConjugatorsStatement : Prop :=
  SmallExponentialConjugatorsStatement F A → ExponentialProductStraighteningStatement F A

set_option maxHeartbeats 3000000 in
theorem exponentialStraighteningFromConjugators : ExponentialStraighteningFromConjugatorsStatement F A := by
  rintro ⟨c₀, hc₀, ε₀, hε₀, U, hBounds, hLip, hExp⟩
  let K := max (1 : ℝ) ‖(1 : A)‖
  have hK : 1 ≤ K := le_max_left _ _
  let c := K * c₀
  have hc : 1 ≤ c := one_le_mul_of_one_le_of_one_le hK hc₀
  have hcPos : 0 < c := zero_lt_one.trans_le hc
  let ε := min ε₀ (1 / (2 * c))
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hcε : c * ε < 1 := by
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hcPos.le).trans_lt
    change c * (1 / (2 * c)) < 1
    field_simp
    linarith
  refine ⟨c, hc, ε, hε, hcε, fun r hr hR => ?_⟩
  let : IsUltrametricDist (A × A) := pairIsUltrametric
  let B := closedBall (0 : A × A) r
  let i (x : B) : closedBall (0 : A × A) ε₀ := ⟨x.val,
    closedBall_subset_closedBall (hR.trans (min_le_left _ _)) x.property⟩
  let w (b : Bool) (x : B) : A := if b then x.val.2 else x.val.1
  let u (b : Bool) (x : B) : Aˣ := U b (i x)
  let δ (x : B) : A × A := (conjugationHomeomorph (u false x) x.val.1 - x.val.1,
    conjugationHomeomorph (u true x) x.val.2 - x.val.2)
  have hzero : δ ⟨0, mem_closedBall_self hr.le⟩ = 0 := by simp [δ]
  have hNorm (x : B) : ‖x.val‖ ≤ r := dist_zero_right x.val ▸ x.property
  have hcoord (b : Bool) (x : B) : ‖w b x‖ ≤ r := by
    have h := hNorm x
    rw [Prod.norm_def, max_le_iff] at h
    cases b
    · exact h.1
    · exact h.2
  have hcoordDiff (b : Bool) (x y : B) : ‖w b x - w b y‖ ≤ ‖x.val - y.val‖ := by
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hC₀le : c₀ ≤ c := le_mul_of_one_le_left (zero_le_one.trans hc₀) hK
  have hcr : c * r < 1 := (mul_le_mul_of_nonneg_left hR hcPos.le).trans_lt hcε
  let k : ℝ≥0 := ⟨c * r, mul_nonneg hcPos.le hr.le⟩
  have hk : k < 1 := by exact_mod_cast hcr
  have hδ (x y : B) : ‖δ x - δ y‖ ≤ (k : ℝ) * ‖x.val - y.val‖ := by
    have hAux (b : Bool) : ‖(conjugationHomeomorph (u b x) (w b x) - w b x) -
        (conjugationHomeomorph (u b y) (w b y) - w b y)‖ ≤ (k : ℝ) * ‖x.val - y.val‖ := by
      have hcr₀ : c₀ * r ≤ 1 := (mul_le_mul_of_nonneg_right hC₀le hr.le).trans hcr.le
      exact norm_displacement_sub_le (zero_le_one.trans hc₀) hr.le (norm_nonneg _) hcr₀
        (hcoord b x) (hcoord b y) (hcoordDiff b x y)
        ((hBounds b (i y)).1.trans (mul_le_mul_of_nonneg_left (hNorm y) (zero_le_one.trans hc₀)))
        (hLip b (i x) (i y)).1 (hBounds b (i x)).2 (hLip b (i x) (i y)).2
    exact max_le (hAux false) (hAux true)
  obtain ⟨Ψ, hΨ⟩ := exists_isometryEquiv_ball_add hr.le δ hzero hk hδ
  let L := closedBall (0 : A) r
  let e := pairBallIsometry (A := A) r
  let Φ : L × L ≃ᵢ L × L := e.symm.trans (Ψ.trans e)
  refine ⟨Φ, fun x => ?_⟩
  let p := e.symm x
  have hΦ : (((Φ x).1 : A), ((Φ x).2 : A)) = ((Ψ p).val : A × A) := rfl
  have hΦ₁ : ((Φ x).1 : A) = conjugationHomeomorph (u false p) x.1.val := by
    rw [← show ((((Φ x).1 : A), ((Φ x).2 : A)) : A × A).1 = ((Φ x).1 : A) from rfl]
    rw [hΦ, hΨ p]
    change x.1.val + (conjugationHomeomorph (u false p) x.1.val - x.1.val) = _
    abel
  have hΦ₂ : ((Φ x).2 : A) = conjugationHomeomorph (u true p) x.2.val := by
    rw [← show ((((Φ x).1 : A), ((Φ x).2 : A)) : A × A).2 = ((Φ x).2 : A) from rfl]
    rw [hΦ, hΨ p]
    change x.2.val + (conjugationHomeomorph (u true p) x.2.val - x.2.val) = _
    abel
  refine ⟨by rw [hΦ₁, hΦ₂]; exact hExp (i p), u false p, u true p, ?_, ?_, hΦ₁, hΦ₂⟩
  · exact ((hBounds false (i p)).1.trans (mul_le_mul_of_nonneg_left (hNorm p) (zero_le_one.trans hc₀))).trans
      (mul_le_mul_of_nonneg_right hC₀le hr.le)
  · exact ((hBounds true (i p)).1.trans (mul_le_mul_of_nonneg_left (hNorm p) (zero_le_one.trans hc₀))).trans
      (mul_le_mul_of_nonneg_right hC₀le hr.le)

end Langlands.HarmonicAnalysis.UnitConjugation
