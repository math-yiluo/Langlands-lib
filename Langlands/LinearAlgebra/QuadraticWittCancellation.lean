import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Tactic.Ring

/-! # Cancellation of a nonzero quadratic line -/

noncomputable section

namespace Langlands

variable {K V V₁ V₂ : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

private def polarReflection (q : QuadraticForm K V) (w : V) (hw : q w ≠ 0) :
    q.IsometryEquiv q := by
  let f : V →ₗ[K] K := (q w)⁻¹ • q.polarBilin w
  have hf : f w = 2 := by
    change (q w)⁻¹ * QuadraticMap.polar q w w = 2
    rw [QuadraticMap.polar_self, two_smul, mul_add, inv_mul_cancel₀ hw, one_add_one_eq_two]
  refine { Module.reflection hf with map_app' := ?_ }
  intro z
  change q (Module.reflection hf z) = q z
  rw [Module.reflection_apply, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add q, q.map_smul,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_comm q z w]
  have h : f z * q w = QuadraticMap.polar q w z := by
    change ((q w)⁻¹ * QuadraticMap.polar q w z) * q w = _
    rw [mul_comm ((q w)⁻¹) _, mul_assoc, inv_mul_cancel₀ hw, mul_one]
  rw [← h]
  simp only [smul_eq_mul]
  ring

private theorem polarReflection_apply (q : QuadraticForm K V) (w : V) (hw : q w ≠ 0)
    (z : V) : polarReflection q w hw z = z - (QuadraticMap.polar q w z / q w) • w := by
  change z - ((q w)⁻¹ * QuadraticMap.polar q w z) • w = _
  rw [div_eq_mul_inv, mul_comm (q w)⁻¹]

private theorem exists_isometryEquiv_of_eq_nonzero_value [Invertible (2 : K)]
    (q : QuadraticForm K V) (x y : V) (h : q x = q y) (hx : q x ≠ 0) :
    ∃ e : q.IsometryEquiv q, e x = y := by
  by_cases hd : q (x - y) = 0
  · have hsum : q (x + y) + q (x - y) = (2 : K) * ((2 : K) * q x) := by
      simp only [sub_eq_add_neg, QuadraticMap.map_add q, q.map_neg,
        QuadraticMap.polar_neg_right, ← h]
      ring
    have hs : q (x + y) ≠ 0 := by
      intro hs
      rw [hs, hd, add_zero] at hsum
      have htwo := Invertible.ne_zero (2 : K)
      exact (mul_ne_zero htwo (mul_ne_zero htwo hx)) hsum.symm
    have hp : QuadraticMap.polar q (x + y) x = q (x + y) := by
      rw [QuadraticMap.polar_add_left, QuadraticMap.polar_self,
        QuadraticMap.polar_comm q y x, QuadraticMap.map_add q, ← h, two_smul]
    let neg : q.IsometryEquiv q := { LinearEquiv.neg K with map_app' := q.map_neg }
    refine ⟨(polarReflection q (x + y) hs).trans neg, ?_⟩
    change -(polarReflection q (x + y) hs x) = y
    rw [polarReflection_apply, hp, div_self hs, one_smul, neg_sub, add_sub_cancel_left]
  · have hp : QuadraticMap.polar q (x - y) x = q (x - y) := by
      simp only [sub_eq_add_neg, QuadraticMap.polar_add_left, QuadraticMap.polar_neg_left,
        QuadraticMap.polar_self, QuadraticMap.map_add q, q.map_neg, QuadraticMap.polar_neg_right,
        QuadraticMap.polar_comm q y x, ← h, two_smul]
    refine ⟨polarReflection q (x - y) hd, ?_⟩
    rw [polarReflection_apply, hp, div_self hd, one_smul, sub_sub_cancel]

private theorem polar_prod_axis (a : K) (q : QuadraticForm K V) (z : K × V) :
    QuadraticMap.polar ((a • (QuadraticMap.sq : QuadraticForm K K)).prod q) (1, 0) z =
      (2 * a) * z.1 := by
  let line : QuadraticForm K K := a • QuadraticMap.sq
  rw [QuadraticMap.polar_prod]
  change QuadraticMap.polar line 1 z.1 + QuadraticMap.polar q 0 z.2 = _
  rw [QuadraticMap.polar_zero_left, add_zero, ← show z.1 • (1 : K) = z.1 by simp,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_self]
  simp [line, two_smul]
  ring

private theorem fst_apply_eq_zero_of_fix_axis [Invertible (2 : K)]
    {a : K} (ha : a ≠ 0) {q₁ : QuadraticForm K V₁} {q₂ : QuadraticForm K V₂}
    (e : ((a • (QuadraticMap.sq : QuadraticForm K K)).prod q₁).IsometryEquiv
      ((a • (QuadraticMap.sq : QuadraticForm K K)).prod q₂))
    (he : e (1, 0) = (1, 0)) (x : V₁) : (e (0, x)).1 = 0 := by
  let line : QuadraticForm K K := a • QuadraticMap.sq
  have h : QuadraticMap.polar (line.prod q₂) (e (1, 0)) (e (0, x)) =
      QuadraticMap.polar (line.prod q₁) (1, 0) (0, x) := by
    simp only [line, QuadraticMap.polar, ← map_add e, e.map_app]
  rw [he, polar_prod_axis, polar_prod_axis] at h
  change (2 * a) * (e (0, x)).1 = (2 * a) * 0 at h
  rw [mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (Invertible.ne_zero (2 : K)) ha)

/-- A common nonzero one-dimensional orthogonal summand can be canceled from an isometry. -/
theorem quadraticForm_equivalent_of_prod_smul_sq [Invertible (2 : K)]
    (a : K) (ha : a ≠ 0) {q₁ : QuadraticForm K V₁} {q₂ : QuadraticForm K V₂}
    (h : ((a • (QuadraticMap.sq : QuadraticForm K K)).prod q₁).Equivalent
      ((a • (QuadraticMap.sq : QuadraticForm K K)).prod q₂)) : q₁.Equivalent q₂ := by
  let line : QuadraticForm K K := a • QuadraticMap.sq
  obtain ⟨e₀⟩ := h
  have hvalue (q : QuadraticForm K V₂) : (line.prod q) (1, 0) = a := by simp [line]
  have hx : (line.prod q₂) (e₀ (1, 0)) = a := by rw [e₀.map_app]; simp
  obtain ⟨r, hr⟩ := exists_isometryEquiv_of_eq_nonzero_value (line.prod q₂)
    (e₀ (1, 0)) (1, 0) (hx.trans (hvalue q₂).symm) (hx.symm ▸ ha)
  let e := e₀.trans r
  have he : e (1, 0) = (1, 0) := hr
  have he' : e.symm (1, 0) = (1, 0) := (e.symm_apply_eq).mpr he.symm
  let f : V₁ →ₗ[K] V₂ :=
    LinearMap.snd K K V₂ ∘ₗ e.toLinearEquiv.toLinearMap ∘ₗ LinearMap.inr K K V₁
  let g : V₂ →ₗ[K] V₁ :=
    LinearMap.snd K K V₁ ∘ₗ e.symm.toLinearEquiv.toLinearMap ∘ₗ LinearMap.inr K K V₂
  have hf (x : V₁) : (0, f x) = e (0, x) :=
    Prod.ext (fst_apply_eq_zero_of_fix_axis ha e he x).symm rfl
  have hg (x : V₂) : (0, g x) = e.symm (0, x) :=
    Prod.ext (fst_apply_eq_zero_of_fix_axis ha e.symm he' x).symm rfl
  have hfg (x : V₂) : f (g x) = x := by
    have hfg : ((0 : K), f (g x)) = (0, x) := by rw [hf, hg, e.apply_symm_apply]
    exact congrArg Prod.snd hfg
  have hgf (x : V₁) : g (f x) = x := by
    have hgf : ((0 : K), g (f x)) = (0, x) := by rw [hg, hf, e.symm_apply_apply]
    exact congrArg Prod.snd hgf
  refine ⟨{ toLinearEquiv := { __ := f, invFun := g, left_inv := hgf, right_inv := hfg }
            map_app' := ?_ }⟩
  intro x
  change q₂ (f x) = q₁ x
  have h := e.map_app (0, x)
  rw [← hf] at h
  simpa [line] using h

end Langlands
