import Langlands.LinearAlgebra.QuadraticWittExtension
import Mathlib.Algebra.Ring.Parity
import Mathlib.LinearAlgebra.Determinant

/-! # Generation of a regular quadratic isometry group by reflections -/

noncomputable section

universe u v

namespace Langlands.QuadraticForm

open QuadraticMap

variable {F : Type u} {V : Type v} [Field F] [AddCommGroup V] [Module F V]
  (Q : QuadraticForm F V)

/-- A list of vectors of nonzero value acts by applying their reflections in list order. -/
def reflectionWord (l : List {x : V // Q x ≠ 0}) : Q.IsometryEquiv Q :=
  l.foldr (fun (x : {z : V // Q z ≠ 0}) e => (reflection Q (x : V) x.property).trans e)
    (IsometryEquiv.refl Q)

@[simp] theorem reflectionWord_nil : reflectionWord Q [] = IsometryEquiv.refl Q := rfl

@[simp] theorem reflectionWord_cons (x : {x : V // Q x ≠ 0})
    (l : List {x : V // Q x ≠ 0}) :
    reflectionWord Q (x :: l) = (reflection Q x x.property).trans (reflectionWord Q l) := rfl

theorem reflectionWord_append (l m : List {x : V // Q x ≠ 0}) :
    reflectionWord Q (l ++ m) = (reflectionWord Q l).trans (reflectionWord Q m) := by
  induction l with
  | nil =>
    apply DFunLike.ext
    intro x
    rfl
  | cons x l ih =>
    rw [List.cons_append, reflectionWord_cons, reflectionWord_cons, ih]
    apply DFunLike.ext
    intro y
    rfl

private theorem exists_reflectionWord_map_vector (h2 : (2 : F) ≠ 0) {x y : V}
    (hxy : Q x = Q y) (hx : Q x ≠ 0) :
    ∃ l : List {z : V // Q z ≠ 0}, reflectionWord Q l x = y ∧
      ∀ w : V, polar Q w x = 0 → polar Q w y = 0 → reflectionWord Q l w = w := by
  have hminus : Q (x - y) = Q x + Q y - polar Q x y := by
    rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q), Q.map_neg, polar_neg_right, sub_eq_add_neg]
  by_cases h : Q (x - y) = 0
  · have hv : Q (x + y) ≠ 0 := by
      rw [hminus, ← hxy] at h
      rw [QuadraticMap.map_add (⇑Q), ← hxy]
      have hmul : Q x + Q x + polar Q x y = (2 : F) * ((2 : F) * Q x) := by
        linear_combination -h
      rw [hmul]
      exact mul_ne_zero h2 (mul_ne_zero h2 hx)
    have hy : Q y ≠ 0 := hxy ▸ hx
    refine ⟨[⟨x + y, hv⟩, ⟨y, hy⟩], ?_, ?_⟩
    · change reflection Q y hy (reflection Q (x + y) hv x) = y
      have hp : polar Q x (x + y) = Q (x + y) := by
        rw [polar_add_right, polar_self, QuadraticMap.map_add (⇑Q), ← hxy, two_smul]
      have hr : reflection Q (x + y) hv x = -y := by
        rw [reflection_apply, hp, div_self hv, one_smul]
        abel
      rw [hr, reflection_apply, polar_neg_left, polar_self, two_smul]
      have hc : -(Q y + Q y) / Q y = (-2 : F) := by field_simp; ring
      rw [hc, neg_smul, sub_neg_eq_add, two_smul]
      abel
    · intro w hwx hwy
      change reflection Q y hy (reflection Q (x + y) hv w) = w
      simp [polar_add_right, hwx, hwy]
  · refine ⟨[⟨x - y, h⟩], ?_, ?_⟩
    · have hp : polar Q x (x - y) = Q (x - y) := by
        rw [polar_sub_right, polar_self, hminus, ← hxy, two_smul]
      change reflection Q (x - y) h x = y
      rw [reflection_apply, hp, div_self h, one_smul, sub_sub_cancel]
    · intro w hwx hwy
      change reflection Q (x - y) h w = w
      simp [polar_sub_right, hwx, hwy]

variable [FiniteDimensional F V] [Invertible (2 : F)]

/-- Every isometry of a regular finite-dimensional quadratic form is a product of reflections. -/
theorem exists_reflectionWord (hQ : Q.polarBilin.Nondegenerate) (g : Q.IsometryEquiv Q) :
    ∃ l : List {z : V // Q z ≠ 0}, reflectionWord Q l = g := by
  classical
  have hs : Q.polarBilin.IsSymm := ⟨fun x y => polar_comm Q x y⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  have hnonzero (i : Fin (Module.finrank F V)) : Q (b i) ≠ 0 := by
    have h := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
      (B := Q.polarBilin) (v := b) hb hQ i
    change polar Q (b i) (b i) ≠ 0 at h
    rw [polar_self] at h
    exact fun hz => h (by rw [hz, smul_zero])
  have hp (f : Q.IsometryEquiv Q) (x y : V) : polar Q (f x) (f y) = polar Q x y := by
    simp only [polar, ← map_add f, IsometryEquiv.map_app]
  have step (s : Finset (Fin (Module.finrank F V))) :
      ∃ l : List {z : V // Q z ≠ 0}, ∀ i ∈ s, reflectionWord Q l (b i) = g (b i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨[], by simp⟩
    | @insert i s hi ih =>
      obtain ⟨l, hl⟩ := ih
      let e := reflectionWord Q l
      obtain ⟨m, hm, hfix⟩ := exists_reflectionWord_map_vector Q
        (Invertible.ne_zero (2 : F)) ((e.map_app (b i)).trans (g.map_app (b i)).symm)
        (by simpa only [IsometryEquiv.map_app] using hnonzero i)
      refine ⟨l ++ m, fun j hj => ?_⟩
      rw [reflectionWord_append]
      change reflectionWord Q m (e (b j)) = g (b j)
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hm
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        have h₁ : polar Q (e (b j)) (e (b i)) = 0 := (hp e _ _).trans (hb hji)
        have h₂ : polar Q (e (b j)) (g (b i)) = 0 := by
          rw [show e (b j) = g (b j) from hl j hj, hp g]
          exact hb hji
        exact (hfix _ h₁ h₂).trans (hl j hj)
  obtain ⟨l, hl⟩ := step Finset.univ
  refine ⟨l, ?_⟩
  have h : (reflectionWord Q l).toLinearEquiv.toLinearMap = g.toLinearEquiv.toLinearMap :=
    b.ext fun i => hl i (Finset.mem_univ i)
  apply DFunLike.ext
  intro x
  exact congrArg (fun f : V →ₗ[F] V => f x) h

/-- A reflection has determinant minus one. -/
theorem det_reflection (z : V) (hz : Q z ≠ 0) :
    (reflection Q z hz).toLinearEquiv.toLinearMap.det = -1 := by
  have hz₀ : z ≠ 0 := fun h => hz (h.symm ▸ map_zero Q)
  have hz₂ : Q.polarBilin z z ≠ 0 := by
    rw [polarBilin_apply_apply, polar_self, two_smul, ← two_mul]
    exact mul_ne_zero (Invertible.ne_zero (2 : F)) hz
  let W := LinearMap.BilinForm.orthogonal Q.polarBilin (F ∙ z)
  let e : (F × W) ≃ₗ[F] V := ((LinearEquiv.toSpanNonzeroSingleton F V z hz₀).prodCongr
    (LinearEquiv.refl F W)).trans
      ((F ∙ z).prodEquivOfIsCompl W (LinearMap.BilinForm.isCompl_span_singleton_orthogonal hz₂))
  let f : F × W →ₗ[F] F × W := (LinearMap.mulLeft F (-1 : F)).prodMap LinearMap.id
  have hp (p : F × W) : e p = p.1 • z + p.2 := rfl
  have h : e.conj f = (reflection Q z hz).toLinearEquiv.toLinearMap := by
    ext y
    obtain ⟨p, rfl⟩ := e.surjective y
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change e ((-1 : F) * p.1, p.2) = reflection Q z hz (e p)
    have hw : polar Q (p.2 : V) z = 0 := by
      rw [polar_comm]
      exact p.2.property z (Submodule.mem_span_singleton_self z)
    rw [neg_one_mul, hp, hp, reflection_apply, polar_add_left, hw, add_zero, polar_smul_left,
      polar_self, two_smul]
    simp only [neg_smul, smul_eq_mul]
    have hc : p.1 * (Q z + Q z) / Q z = p.1 + p.1 := by field_simp
    rw [hc, add_smul]
    abel
  rw [← h]
  change LinearMap.det ((e : (F × W) →ₗ[F] V) ∘ₗ f ∘ₗ (e.symm : V →ₗ[F] (F × W))) = -1
  rw [LinearMap.det_conj]
  simp only [f, LinearMap.det_prodMap, LinearMap.det_mulLeft, LinearMap.det_id, mul_one]

/-- The determinant of a reflection word is determined by its length parity. -/
theorem det_reflectionWord (l : List {z : V // Q z ≠ 0}) :
    (reflectionWord Q l).toLinearEquiv.toLinearMap.det = (-1 : F) ^ l.length := by
  induction l with
  | nil => simp [reflectionWord, IsometryEquiv.refl]
  | cons z l ih =>
    change (((reflectionWord Q l).toLinearEquiv.toLinearMap).comp
      (reflection Q z z.property).toLinearEquiv.toLinearMap).det = _
    rw [LinearMap.det_comp, ih, det_reflection, List.length_cons, pow_succ]

/-- An orientation-preserving isometry has a reflection expression of even length. -/
theorem exists_even_reflectionWord (hQ : Q.polarBilin.Nondegenerate) (g : Q.IsometryEquiv Q)
    (hg : g.toLinearEquiv.toLinearMap.det = 1) :
    ∃ l : List {z : V // Q z ≠ 0}, Even l.length ∧ reflectionWord Q l = g := by
  obtain ⟨l, hl⟩ := exists_reflectionWord Q hQ g
  have hne : (-1 : F) ≠ 1 := by
    intro h
    apply Invertible.ne_zero (2 : F)
    linear_combination -h
  refine ⟨l, (neg_one_pow_eq_one_iff_even hne).mp ?_, hl⟩
  rw [← det_reflectionWord Q, hl, hg]

end Langlands.QuadraticForm
