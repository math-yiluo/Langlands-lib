import Langlands.Group.AlgebraicPolar
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Minimal vectors have star-stable stabilizers -/

noncomputable section

universe u

namespace Langlands.Group.MinimalVector

open Matrix
open Langlands.Group.AlgebraicPolar
open scoped ComplexOrder InnerProductSpace

variable {𝕜 : Type u} [RCLike 𝕜] {n m : Type} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

/-- The action of a matrix unit through `π` on Euclidean coordinate space. -/
def act (π : GL n 𝕜 →* GL m 𝕜) (g : GL n 𝕜) :
    EuclideanSpace 𝕜 m →L[𝕜] EuclideanSpace 𝕜 m :=
  Matrix.toEuclideanCLM (n := m) (𝕜 := 𝕜) (((π g : GL m 𝕜) : Matrix m m 𝕜))

theorem act_mul (π : GL n 𝕜 →* GL m 𝕜) (g h : GL n 𝕜) (w : EuclideanSpace 𝕜 m) :
    act π (g * h) w = act π g (act π h w) := by
  simp only [act, map_mul, Units.val_mul]
  rfl

theorem act_one (π : GL n 𝕜 →* GL m 𝕜) (w : EuclideanSpace 𝕜 m) :
    act π 1 w = w := by
  simp only [act, map_one, Units.val_one]
  rfl

/-- The stabilizer of a vector for the action through `π`. -/
def stabilizer (π : GL n 𝕜 →* GL m 𝕜) (w : EuclideanSpace 𝕜 m) : Subgroup (GL n 𝕜) where
  carrier := {g | act π g w = w}
  mul_mem' {a b} ha hb := by
    change act π (a * b) w = w
    rw [act_mul, hb, ha]
  one_mem' := act_one π w
  inv_mem' {a} ha := by
    change act π a⁻¹ w = w
    conv_lhs => rw [← ha]
    rw [← act_mul, inv_mul_cancel, act_one]

theorem mem_stabilizer_iff (π : GL n 𝕜 →* GL m 𝕜) (w : EuclideanSpace 𝕜 m) (g : GL n 𝕜) :
    g ∈ stabilizer π w ↔ act π g w = w :=
  Iff.rfl

/-- A vector is minimal when no vector in its orbit has smaller norm. -/
def IsMinimalVector (π : GL n 𝕜 →* GL m 𝕜) (w : EuclideanSpace 𝕜 m) : Prop :=
  ∀ g : GL n 𝕜, ‖w‖ ≤ ‖act π g w‖

theorem inner_apply_eq_of_isSelfAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (R : E →L[𝕜] E) (hR : IsSelfAdjoint R)
    (x y : E) : ⟪R x, y⟫_𝕜 = ⟪x, R y⟫_𝕜 := by
  calc ⟪R x, y⟫_𝕜 = ⟪(ContinuousLinearMap.adjoint R) x, y⟫_𝕜 := by
        rw [← ContinuousLinearMap.star_eq_adjoint, hR.star_eq]
    _ = ⟪x, R y⟫_𝕜 := ContinuousLinearMap.adjoint_inner_left R y x

/-- If a self-adjoint operator does not decrease the norm of `w` and its square does not
increase it, then its square fixes `w`. -/
theorem sq_apply_eq_of_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (R : E →L[𝕜] E) (hR : IsSelfAdjoint R) (w : E)
    (h₁ : ‖w‖ ≤ ‖R w‖) (h₂ : ‖R (R w)‖ ≤ ‖w‖) : R (R w) = w := by
  have hinner : RCLike.re ⟪R (R w), w⟫_𝕜 = ‖R w‖ ^ 2 := by
    rw [inner_apply_eq_of_isSelfAdjoint R hR (R w) w]
    exact inner_self_eq_norm_sq (𝕜 := 𝕜) (R w)
  have hsq : ‖R (R w) - w‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq (𝕜 := 𝕜), hinner]
    have h0 : 0 ≤ ‖w‖ := norm_nonneg _
    have h0' : 0 ≤ ‖R (R w)‖ := norm_nonneg _
    nlinarith
  have hzero : ‖R (R w) - w‖ = 0 := by
    have := sq_nonneg ‖R (R w) - w‖
    nlinarith [norm_nonneg (R (R w) - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem act_star (π : GL n 𝕜 →* GL m 𝕜) (hπ : ∀ g, π (star g) = star (π g)) (g : GL n 𝕜) :
    act π (star g) = star (act π g) := by
  simp only [act, hπ, Units.coe_star, map_star]

theorem isSelfAdjoint_act (π : GL n 𝕜 →* GL m 𝕜) (hπ : ∀ g, π (star g) = star (π g))
    (p : GL n 𝕜) (hp : p.val.PosDef) : IsSelfAdjoint (act π p) := by
  have hstar : star p = p := Units.ext (by rw [Units.coe_star]; exact hp.isHermitian)
  change star (act π p) = act π p
  rw [← act_star π hπ, hstar]

theorem inner_act_star_mul (π : GL n 𝕜 →* GL m 𝕜) (hπ : ∀ g, π (star g) = star (π g))
    (g : GL n 𝕜) (x y : EuclideanSpace 𝕜 m) :
    ⟪act π (star g * g) x, y⟫_𝕜 = ⟪act π g x, act π g y⟫_𝕜 := by
  rw [act_mul, act_star π hπ, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

/-- **Minimal vectors.** For a representation compatible with conjugate transpose, the
stabilizer of a minimal vector is stable under conjugate transpose. -/
theorem star_mem_stabilizer (π : GL n 𝕜 →* GL m 𝕜) (hπ : ∀ g, π (star g) = star (π g))
    {w : EuclideanSpace 𝕜 m} (hw : IsMinimalVector π w) {g : GL n 𝕜}
    (hg : g ∈ stabilizer π w) : star g ∈ stabilizer π w := by
  rw [mem_stabilizer_iff] at hg ⊢
  set h : GL n 𝕜 := star g * g with hh_def
  have hh : h.val.PosDef := by
    rw [hh_def, Units.val_mul, Units.coe_star, Matrix.star_eq_conjTranspose]
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_iff_isUnit.mpr g.isUnit)
  set s : GL n 𝕜 := positivePower h hh (1 / 2) with hs_def
  set r : GL n 𝕜 := positivePower h hh (1 / 4) with hr_def
  have hrr : r * r = s := by
    rw [hr_def, hs_def, ← positivePower_add]
    norm_num
  have hss : s * s = h := positivePower_half_sq h hh
  have hsa : IsSelfAdjoint (act π s) := isSelfAdjoint_act π hπ s (positivePower_posDef h hh _)
  have hra : IsSelfAdjoint (act π r) := isSelfAdjoint_act π hπ r (positivePower_posDef h hh _)
  have hs_sq : ‖act π s w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← inner_self_eq_norm_sq (𝕜 := 𝕜),
      ← inner_apply_eq_of_isSelfAdjoint _ hsa (act π s w) w]
    change RCLike.re ⟪act π s (act π s w), w⟫_𝕜 = _
    rw [← act_mul, hss, hh_def, inner_act_star_mul π hπ, hg]
  have hs_norm : ‖act π s w‖ = ‖w‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hs_sq
  have hsw : act π s w = w := by
    have := sq_apply_eq_of_norm_le (act π r) hra w (hw r)
      (by rw [← act_mul, hrr, hs_norm])
    rwa [← act_mul, hrr] at this
  have hhw : act π h w = w := by
    rw [← hss, act_mul, hsw, hsw]
  rwa [hh_def, act_mul, hg] at hhw

/-- Conjugating by `x` identifies the stabilizer of `x • w` with that of `w`. -/
theorem mem_stabilizer_act_iff (π : GL n 𝕜 →* GL m 𝕜) (w : EuclideanSpace 𝕜 m)
    (x g : GL n 𝕜) :
    g ∈ stabilizer π (act π x w) ↔ x⁻¹ * g * x ∈ stabilizer π w := by
  simp only [mem_stabilizer_iff, act_mul]
  constructor
  · intro h
    rw [h, ← act_mul, inv_mul_cancel, act_one]
  · intro h
    have := congrArg (act π x) h
    rwa [← act_mul, mul_inv_cancel, act_one] at this

/-- A closed orbit contains a minimal vector. -/
theorem exists_isMinimalVector_of_isClosed (π : GL n 𝕜 →* GL m 𝕜) (w : EuclideanSpace 𝕜 m)
    (hclosed : IsClosed (Set.range fun g : GL n 𝕜 => act π g w)) :
    ∃ x : GL n 𝕜, IsMinimalVector π (act π x w) := by
  obtain ⟨_, ⟨x, rfl⟩, hy⟩ := hclosed.exists_infDist_eq_dist ⟨w, 1, act_one π w⟩ 0
  refine ⟨x, fun g => ?_⟩
  have hmem : act π (g * x) w ∈ Set.range fun g : GL n 𝕜 => act π g w := ⟨g * x, rfl⟩
  have h := Metric.infDist_le_dist_of_mem (x := (0 : EuclideanSpace 𝕜 m)) hmem
  rwa [hy, dist_zero_left, dist_zero_left, act_mul] at h

/-- **Closed orbits.** If the orbit of `w` is closed, then some conjugate of the stabilizer
of `w` is stable under conjugate transpose: there is `x` such that `x⁻¹ * g * x` in the
stabilizer implies `x⁻¹ * star g * x` in the stabilizer. -/
theorem exists_conj_star_mem_stabilizer (π : GL n 𝕜 →* GL m 𝕜)
    (hπ : ∀ g, π (star g) = star (π g)) (w : EuclideanSpace 𝕜 m)
    (hclosed : IsClosed (Set.range fun g : GL n 𝕜 => act π g w)) :
    ∃ x : GL n 𝕜, ∀ g : GL n 𝕜,
      x⁻¹ * g * x ∈ stabilizer π w → x⁻¹ * star g * x ∈ stabilizer π w := by
  obtain ⟨x, hx⟩ := exists_isMinimalVector_of_isClosed π w hclosed
  refine ⟨x, fun g hg => ?_⟩
  rw [← mem_stabilizer_act_iff] at hg ⊢
  exact star_mem_stabilizer π hπ hx hg

end Langlands.Group.MinimalVector
