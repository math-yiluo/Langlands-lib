import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Extension of isometries from a nondegenerate quadratic space -/

noncomputable section

universe u v w

namespace Langlands.QuadraticForm

open QuadraticMap

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
  (Q : QuadraticForm F V)

private def reflectionMap (z : V) : V →ₗ[F] V :=
  LinearMap.id - (Q.polarBilin.flip z).smulRight ((Q z)⁻¹ • z)

private theorem reflectionMap_apply (z x : V) :
    reflectionMap Q z x = x - (polar Q x z / Q z) • z := by
  simp only [reflectionMap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.flip_apply, polarBilin_apply_apply, smul_smul, div_eq_mul_inv]

/-- Reflection in a vector of nonzero quadratic value. -/
def reflection (z : V) (hz : Q z ≠ 0) : Q.IsometryEquiv Q where
  toLinearEquiv := LinearEquiv.ofInvolutive (reflectionMap Q z) (by
    intro x
    simp only [reflectionMap_apply, polar_sub_left, polar_smul_left, polar_self, nsmul_eq_mul,
      Nat.cast_ofNat, smul_eq_mul]
    have hc : (polar Q x z - (polar Q x z / Q z) * (2 * Q z)) / Q z =
        -(polar Q x z / Q z) := by field_simp; ring
    rw [hc, neg_smul, sub_neg_eq_add, sub_add_cancel])
  map_app' x := by
    change Q (reflectionMap Q z x) = Q x
    rw [reflectionMap_apply, sub_eq_add_neg, QuadraticMap.map_add (⇑Q), Q.map_neg,
      Q.map_smul, smul_eq_mul, polar_neg_right, polar_smul_right, smul_eq_mul]
    field_simp
    ring

@[simp] theorem reflection_apply (z : V) (hz : Q z ≠ 0) (x : V) :
    reflection Q z hz x = x - (polar Q x z / Q z) • z := reflectionMap_apply Q z x

private theorem polar_sub_value (x y : V) : Q (x - y) = Q x + Q y - polar Q x y := by
  rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q), Q.map_neg, polar_neg_right, sub_eq_add_neg]

/-- Vectors of the same nonzero value are conjugate by an isometry fixing their
common orthogonal subspace pointwise. -/
theorem exists_isometryEquiv_map_vector (h2 : (2 : F) ≠ 0) {x y : V}
    (hxy : Q x = Q y) (hx : Q x ≠ 0) :
    ∃ e : Q.IsometryEquiv Q, e x = y ∧
      ∀ w : V, polar Q w x = 0 → polar Q w y = 0 → e w = w := by
  by_cases hsub : Q (x - y) = 0
  · have hadd : Q (x + y) ≠ 0 := by
      rw [polar_sub_value Q, ← hxy] at hsub
      rw [QuadraticMap.map_add (⇑Q), ← hxy]
      have h : Q x + Q x + polar Q x y = (2 : F) * ((2 : F) * Q x) := by linear_combination -hsub
      rw [h]
      exact mul_ne_zero h2 (mul_ne_zero h2 hx)
    have hy : Q y ≠ 0 := hxy ▸ hx
    refine ⟨(reflection Q (x + y) hadd).trans (reflection Q y hy), ?_, ?_⟩
    · have h : polar Q x (x + y) = Q (x + y) := by
        rw [polar_add_right, polar_self, QuadraticMap.map_add (⇑Q), ← hxy, two_smul]
      change reflection Q y hy (reflection Q (x + y) hadd x) = y
      have hr : reflection Q (x + y) hadd x = -y := by
        rw [reflection_apply, h, div_self hadd, one_smul]
        abel
      rw [hr, reflection_apply, polar_neg_left, polar_self, two_smul]
      have hc : -(Q y + Q y) / Q y = (-2 : F) := by field_simp; ring
      rw [hc, neg_smul, sub_neg_eq_add, two_smul]
      abel
    · intro w hwx hwy
      change reflection Q y hy (reflection Q (x + y) hadd w) = w
      simp [polar_add_right, hwx, hwy]
  · have h : polar Q x (x - y) = Q (x - y) := by
      rw [polar_sub_right, polar_self, polar_sub_value Q, ← hxy, two_smul]
    refine ⟨reflection Q (x - y) hsub, ?_, ?_⟩
    · rw [reflection_apply, h, div_self hsub, one_smul, sub_sub_cancel]
    · intro w hwx hwy
      simp [polar_sub_right, hwx, hwy]

private theorem isometry_map_polar (e : Q.IsometryEquiv Q) (x y : V) :
    polar Q (e x) (e y) = polar Q x y := by
  simp only [polar, ← map_add e, IsometryEquiv.map_app]

private theorem exists_isometryEquiv_match_family {ι : Type*} (s : Finset ι) (h2 : (2 : F) ≠ 0)
    (x y : ι → V) (hx : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0)
    (hy : ∀ i j, i ≠ j → polar Q (y i) (y j) = 0)
    (hval : ∀ i, Q (x i) = Q (y i)) (hnonzero : ∀ i, Q (x i) ≠ 0) :
    ∃ e : Q.IsometryEquiv Q, ∀ i ∈ s, e (x i) = y i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨IsometryEquiv.refl Q, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨a, ha, hf⟩ := exists_isometryEquiv_map_vector Q h2
      ((e.map_app (x i)).trans (hval i)) (by simpa using hnonzero i)
    refine ⟨e.trans a, fun j hj => ?_⟩
    change a (e (x j)) = y j
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ha
    · have hji : j ≠ i := fun h => hi (h ▸ hj)
      apply hf _ _ (by rw [he j hj]; exact hy j i hji) |>.trans (he j hj)
      rw [isometry_map_polar Q e]
      exact hx j i hji

variable {U : Type w} [AddCommGroup U] [Module F U] [FiniteDimensional F U] [Invertible (2 : F)]

/-- Two isometric linear embeddings of a finite-dimensional nondegenerate form into the same
quadratic space differ by an isometry of the ambient form. -/
theorem exists_isometryEquiv_match_embeddings (S : QuadraticForm F U) (hS : S.polarBilin.Nondegenerate)
    (f g : U →ₗ[F] V) (hf : ∀ x, Q (f x) = S x) (hg : ∀ x, Q (g x) = S x) :
    ∃ e : Q.IsometryEquiv Q, ∀ x, e (f x) = g x := by
  classical
  have hSymm : S.polarBilin.IsSymm := ⟨fun x y => polar_comm S x y⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hSymm
  have hn (i : Fin (Module.finrank F U)) : S (b i) ≠ 0 := by
    have h := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
      (B := S.polarBilin) (v := b) hb hS i
    change polar S (b i) (b i) ≠ 0 at h
    rw [polar_self] at h
    exact fun hz => h (by rw [hz, smul_zero])
  have hfP (x y : U) : polar Q (f x) (f y) = polar S x y := by
    simp only [polar, ← map_add f, hf]
  have hgP (x y : U) : polar Q (g x) (g y) = polar S x y := by
    simp only [polar, ← map_add g, hg]
  obtain ⟨e, he⟩ := exists_isometryEquiv_match_family Q Finset.univ
    (isUnit_of_invertible (2 : F)).ne_zero (fun i => f (b i)) (fun i => g (b i))
    (fun i j hij => (hfP _ _).trans (hb hij))
    (fun i j hij => (hgP _ _).trans (hb hij))
    (fun i => (hf _).trans (hg _).symm) (fun i => by rw [hf]; exact hn i)
  have heq : e.toLinearEquiv.toLinearMap.comp f = g :=
    b.ext fun i => he i (Finset.mem_univ i)
  exact ⟨e, fun x => DFunLike.congr_fun heq x⟩

end Langlands.QuadraticForm
