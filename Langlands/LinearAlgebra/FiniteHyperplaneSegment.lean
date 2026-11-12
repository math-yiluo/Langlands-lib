import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Tactic

/-! # Generic rational segments for finite hyperplane arrangements -/

noncomputable section

namespace Langlands.LinearAlgebra.FiniteHyperplaneSegment

variable {ι V : Type*} [Finite ι] [AddCommGroup V] [Module ℚ V]

/-- All forms in a finite family are nonzero at the specified vector. -/
def Regular (f : ι → Module.Dual ℚ V) (x : V) : Prop :=
  ∀ i, f i x ≠ 0

/-- Two regular vectors have strictly matching signs for every form. -/
def SameChamber (f : ι → Module.Dual ℚ V) (x y : V) : Prop :=
  ∀ i, 0 < f i x * f i y

/-- The determinant form detecting simultaneous crossings from a fixed start. -/
def crossingDeterminant (x : V) (f g : Module.Dual ℚ V) : Module.Dual ℚ V :=
  f x • g - g x • f

/-- A rational segment, with its start at parameter zero and end at one. -/
def segment (x y : V) (t : ℚ) : V := (1 - t) • x + t • y

/-- A finite arrangement has a regular point that preserves every sign already
nonzero at a specified vector, even if that vector lies on some walls. -/
theorem exists_regular_preserving_signs (f : ι → Module.Dual ℚ V)
    (hf : ∀ i, f i ≠ 0) (y : V) :
    ∃ z, Regular f z ∧ ∀ i, f i y ≠ 0 → 0 < f i y * f i z := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f (fun i => by
    by_contra! h
    exact hf i (LinearMap.ext h))
  let c : ℚ := 1 + ∑ i, |f i v / f i y|
  have hc (i : ι) : 0 < c + f i v / f i y := by
    have hs : |f i v / f i y| ≤ ∑ j, |f j v / f j y| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (f j v / f j y)) (Finset.mem_univ i)
    have hn := neg_abs_le (f i v / f i y)
    dsimp [c]
    linarith
  have hp (i : ι) (hi : f i y ≠ 0) : 0 < f i y * f i (c • y + v) := by
    have he : f i y * f i (c • y + v) =
        (f i y) ^ 2 * (c + f i v / f i y) := by
      simp only [map_add, map_smul, smul_eq_mul]
      field_simp
    rw [he]
    exact mul_pos (sq_pos_of_ne_zero hi) (hc i)
  refine ⟨c • y + v, ?_, hp⟩
  intro i
  by_cases hi : f i y = 0
  · simpa [hi] using hv i
  · exact (mul_ne_zero_iff.mp (ne_of_gt (hp i hi))).2

/-- Perturbing the end within its chamber makes every nontrivial determinant
form nonzero. No finite-dimensionality assumption is required. -/
theorem exists_generic_endpoint (f : ι → Module.Dual ℚ V) {x y : V}
    (hx : Regular f x) (hy : Regular f y) :
    ∃ z, Regular f z ∧ SameChamber f y z ∧
      ∀ i j, crossingDeterminant x (f i) (f j) ≠ 0 →
        crossingDeterminant x (f i) (f j) z ≠ 0 := by
  classical
  let D := {p : ι × ι // crossingDeterminant x (f p.1) (f p.2) ≠ 0}
  let F : Sum ι D → Module.Dual ℚ V := fun a => match a with
    | .inl i => f i
    | .inr p => crossingDeterminant x (f p.val.1) (f p.val.2)
  have hF (a : Sum ι D) : F a ≠ 0 := by
    rcases a with i | p
    · intro h
      exact hx i (by simp [F, h])
    · exact p.property
  obtain ⟨z, hz, hs⟩ := exists_regular_preserving_signs F hF y
  refine ⟨z, (fun i => hz (.inl i)), (fun i => hs (.inl i) (hy i)), ?_⟩
  intro i j h
  exact hz (.inr ⟨(i, j), h⟩)

/-- A root that has the same strict sign at both ends never vanishes on the
closed segment. This is the wall-avoidance property used for restricted roots. -/
theorem apply_segment_ne_zero_of_mul_pos (f : Module.Dual ℚ V) {x y : V}
    (h : 0 < f x * f y) {t : ℚ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    f (segment x y t) ≠ 0 := by
  simp only [segment, map_add, map_smul, smul_eq_mul]
  rcases mul_pos_iff.mp h with h | h
  · have hp : 0 < (1 - t) * f x + t * f y := by
      by_cases ht0 : t = 0
      · simpa [ht0] using h.1
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr ht') h.1.le) (mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) h.2)
    exact ne_of_gt hp
  · have hn : (1 - t) * f x + t * f y < 0 := by
      by_cases ht0 : t = 0
      · simpa [ht0] using h.1
      · exact add_neg_of_nonpos_of_neg
          (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht') h.1.le)
          (mul_neg_of_pos_of_neg (lt_of_le_of_ne ht (Ne.symm ht0)) h.2)
    exact ne_of_lt hn

/-- At a simultaneous segment crossing the corresponding determinant vanishes. -/
theorem crossingDeterminant_apply_eq_zero {f g : Module.Dual ℚ V} {x y : V}
    (hx : f x ≠ 0) {t : ℚ} (hf : f (segment x y t) = 0)
    (hg : g (segment x y t) = 0) : crossingDeterminant x f g y = 0 := by
  have ht : t ≠ 0 := by
    intro h
    exact hx (by simpa [segment, h] using hf)
  simp only [segment, map_add, map_smul, smul_eq_mul] at hf hg
  change f x * g y - g x * f y = 0
  have h : t * (f x * g y - g x * f y) = 0 := by
    linear_combination f x * hg - g x * hf
  exact (mul_eq_zero.mp h).resolve_left ht

/-- For a generic endpoint, only proportional forms can vanish together. -/
theorem crossingDeterminant_eq_zero_of_generic {f g : Module.Dual ℚ V} {x y : V}
    (hx : f x ≠ 0)
    (hgen : crossingDeterminant x f g ≠ 0 → crossingDeterminant x f g y ≠ 0)
    {t : ℚ} (hf : f (segment x y t) = 0) (hg : g (segment x y t) = 0) :
    crossingDeterminant x f g = 0 := by
  by_contra h
  exact hgen h (crossingDeterminant_apply_eq_zero hx hf hg)

/-- A zero determinant form identifies the two forms up to the explicit scalar
ratio of their values at the regular start. -/
theorem eq_smul_of_crossingDeterminant_eq_zero {f g : Module.Dual ℚ V} {x : V}
    (hx : f x ≠ 0) (h : crossingDeterminant x f g = 0) :
    g = (g x / f x) • f := by
  apply LinearMap.ext
  intro z
  have hz := congrArg (fun a : Module.Dual ℚ V => a z) h
  change f x * g z - g x * f z = 0 at hz
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hx).mpr
  nlinarith

/-- A generic segment between chambers meets just one proportional class of
forms at each crossing, while keeping the endpoint in the specified chamber. -/
theorem exists_segment_with_proportional_crossings (f : ι → Module.Dual ℚ V)
    {x y : V} (hx : Regular f x) (hy : Regular f y) :
    ∃ z, Regular f z ∧ SameChamber f y z ∧
      ∀ (t : ℚ) (i j : ι), f i (segment x z t) = 0 →
        f j (segment x z t) = 0 → ∃ c : ℚ, c ≠ 0 ∧ f j = c • f i := by
  obtain ⟨z, hz, hs, hg⟩ := exists_generic_endpoint f hx hy
  refine ⟨z, hz, hs, ?_⟩
  intro t i j hi hj
  exact ⟨f j x / f i x, div_ne_zero (hx j) (hx i),
    eq_smul_of_crossingDeterminant_eq_zero (hx i)
      (crossingDeterminant_eq_zero_of_generic (hx i) (hg i j) hi hj)⟩

end Langlands.LinearAlgebra.FiniteHyperplaneSegment
