import Langlands.GroupScheme.Composition.CayleyAutomorphismGroup
import Langlands.LinearAlgebra.GramQuadraticComparison
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Coefficient extension of Cayley data -/

noncomputable section

universe u

open Module LinearMap Matrix

namespace Langlands.GroupScheme.CayleyDatum

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] (c : CayleyDatum K)
variable {A B : Type u} [CommRing A] [CommRing B]

theorem map_multiplicationOver_vec (φ : K →+* A) (f : A →+* B) (x y : CayleyVector A) :
    (fun i => f (c.multiplicationOver φ x y i)) =
      c.multiplicationOver (f.comp φ) (fun i => f (x i)) (fun i => f (y i)) :=
  funext fun i => c.map_multiplicationOver φ f x y i

theorem map_unitOver (φ : K →+* A) (f : A →+* B) :
    (fun i => f (c.unitOver φ i)) = c.unitOver (f.comp φ) := rfl

variable [Invertible (2 : K)]

/-- The norm with its symmetric Gram coefficients mapped to `A`. -/
def normOver (φ : K →+* A) : QuadraticForm A (CayleyVector A) :=
  (c.norm.toMatrix'.map φ).toQuadraticForm'

theorem normOver_apply (φ : K →+* A) (x : CayleyVector A) :
    c.normOver φ x = ∑ i, ∑ j, x i * φ (c.norm.toMatrix' i j) * x j := by
  simp only [normOver, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, Matrix.map_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem map_normOver (φ : K →+* A) (f : A →+* B) (x : CayleyVector A) :
    f (c.normOver φ x) = c.normOver (f.comp φ) (fun i => f (x i)) := by
  simp only [normOver_apply, map_sum, map_mul, RingHom.comp_apply]

@[simp] theorem normOver_self : c.normOver (RingHom.id K) = c.norm := by
  unfold normOver
  rw [show c.norm.toMatrix'.map (RingHom.id K) = c.norm.toMatrix' from rfl]
  change LinearMap.BilinMap.toQuadraticMap
    (Matrix.toLinearMap₂' K (S₁ := K) (S₂ := K) (LinearMap.toMatrix₂' K c.norm.associated)) = c.norm
  rw [Matrix.toLinearMap₂'_toMatrix', QuadraticMap.toQuadraticMap_associated]

/-- The extended norm on coordinates is the tensor scalar extension of the original norm. -/
def baseChangeNormIsometry [Algebra K A] :
    (c.norm.baseChange A).IsometryEquiv (c.normOver (algebraMap K A)) := by
  have h : c.norm.toMatrix'.toQuadraticForm' = c.norm := c.normOver_self
  rw [← h]
  exact Langlands.LinearAlgebra.OrthogonalCocycleDescent.gramBaseChangeIsometry c.norm.toMatrix'

omit [Invertible (2 : K)] in
private theorem multiplicationOver_unit_left (φ : K →+* A) (x : CayleyVector A) :
    c.multiplicationOver φ (c.unitOver φ) x = x := by
  let L := c.multiplicationBilin φ (c.unitOver φ)
  have h : L = LinearMap.id := by
    apply (Pi.basisFun A (Fin 8)).ext
    intro i
    simp only [Pi.basisFun_apply, LinearMap.id_apply]
    change c.multiplicationOver φ (c.unitOver φ) (Pi.single i 1) = Pi.single i 1
    have he := c.map_multiplicationOver_vec (RingHom.id K) φ c.unit (Pi.single i 1)
    have hs : (fun j => φ ((Pi.single i (1 : K) : CayleyVector K) j)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [c.multiplicationOver_self, c.unit_mul, hs, RingHom.comp_id] at he
    exact he.symm
  exact LinearMap.congr_fun h x

omit [Invertible (2 : K)] in
private theorem multiplicationOver_unit_right (φ : K →+* A) (x : CayleyVector A) :
    c.multiplicationOver φ x (c.unitOver φ) = x := by
  let L := (c.multiplicationBilin φ).flip (c.unitOver φ)
  have h : L = LinearMap.id := by
    apply (Pi.basisFun A (Fin 8)).ext
    intro i
    simp only [Pi.basisFun_apply, LinearMap.id_apply]
    change c.multiplicationOver φ (Pi.single i 1) (c.unitOver φ) = Pi.single i 1
    have he := c.map_multiplicationOver_vec (RingHom.id K) φ (Pi.single i 1) c.unit
    have hs : (fun j => φ ((Pi.single i (1 : K) : CayleyVector K) j)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [c.multiplicationOver_self, c.mul_unit, hs, RingHom.comp_id] at he
    exact he.symm
  exact LinearMap.congr_fun h x

private theorem normOver_unit (φ : K →+* A) : c.normOver φ (c.unitOver φ) = 1 := by
  have h := c.map_normOver (RingHom.id K) φ c.unit
  rw [normOver_self, c.norm_unit, map_one, RingHom.comp_id] at h
  exact h.symm

private theorem normOver_mul [Infinite K] (φ : K →+* A) (x y : CayleyVector A) :
    c.normOver φ (c.multiplicationOver φ x y) = c.normOver φ x * c.normOver φ y := by
  let R := MvPolynomial (Fin 8 ⊕ Fin 8) K
  let p : K →+* R := MvPolynomial.C
  let X : CayleyVector R := fun i => MvPolynomial.X (Sum.inl i)
  let Y : CayleyVector R := fun i => MvPolynomial.X (Sum.inr i)
  have h : c.normOver p (c.multiplicationOver p X Y) = c.normOver p X * c.normOver p Y := by
    apply MvPolynomial.funext
    intro v
    let e : R →+* K := MvPolynomial.eval v
    have he : e.comp p = RingHom.id K := by
      ext k
      exact MvPolynomial.eval_C k
    change e (c.normOver p (c.multiplicationOver p X Y)) = e (c.normOver p X * c.normOver p Y)
    rw [map_mul, c.map_normOver, c.map_normOver, c.map_normOver,
      c.map_multiplicationOver_vec, he, c.normOver_self, c.multiplicationOver_self]
    exact c.norm_mul _ _
  let e : R →+* A := MvPolynomial.eval₂Hom φ (Sum.elim x y)
  have he : e.comp p = φ := by
    ext k
    exact MvPolynomial.eval₂Hom_C φ _ k
  have hx : (fun i => e (X i)) = x := by
    funext i
    exact MvPolynomial.eval₂Hom_X' φ _ (Sum.inl i)
  have hy : (fun i => e (Y i)) = y := by
    funext i
    exact MvPolynomial.eval₂Hom_X' φ _ (Sum.inr i)
  have h' := congrArg e h
  rwa [map_mul, c.map_normOver, c.map_normOver, c.map_normOver, c.map_multiplicationOver_vec,
    he, hx, hy] at h'

private theorem normOver_nondegenerate {L : Type u} [Field L] (φ : K →+* L) :
    (c.normOver φ).polarBilin.Nondegenerate := by
  let D := c.norm.toMatrix'
  have hD : D.IsSymm := c.norm.isSymm_toMatrix'
  have hA : (c.norm.associated : LinearMap.BilinForm K (CayleyVector K)).Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro x hx
    apply c.polar_nondegenerate x
    intro y
    rw [← QuadraticMap.two_nsmul_associated K c.norm, two_nsmul, LinearMap.add_apply,
      LinearMap.add_apply, hx y, add_zero]
  have hdet : D.det ≠ 0 := by
    apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp
    change (Matrix.toLinearMap₂' K (S₁ := K) (S₂ := K)
      (LinearMap.toMatrix₂' K c.norm.associated)).Nondegenerate
    rwa [Matrix.toLinearMap₂'_toMatrix']
  have hL : (D.map φ).toBilin'.Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
    change (φ.mapMatrix D).det ≠ 0
    rw [← φ.map_det]
    exact (map_ne_zero φ).mpr hdet
  have ht : (2 : L) ≠ 0 := by
    rw [← map_ofNat φ 2]
    exact (map_ne_zero φ).mpr (isUnit_of_invertible (2 : K)).ne_zero
  have hs : (D.map φ).IsSymm := by
    ext i j
    exact congrArg φ (congrFun (congrFun hD i) j)
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  apply hL.1 x
  intro y
  have hxy := hx y
  change ((D.map φ).toBilin'.toQuadraticMap).polarBilin x y = 0 at hxy
  have hsym : (D.map φ).toBilin' y x = (D.map φ).toBilin' x y :=
    Langlands.LinearAlgebra.OrthogonalCocycleDescent.bilinear_symm_of_matrix_symm hs y x
  rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, LinearMap.add_apply,
    LinearMap.add_apply, LinearMap.flip_apply, hsym, ← two_mul] at hxy
  exact (mul_eq_zero.mp hxy).resolve_left ht

/-- Coefficient extension of a Cayley datum over an infinite field of characteristic
  different from two. -/
def extend [Infinite K] {L : Type u} [Field L] (φ : K →+* L) : CayleyDatum L where
  multiplication := c.multiplicationBilin φ
  unit := c.unitOver φ
  norm := c.normOver φ
  unit_mul := c.multiplicationOver_unit_left φ
  mul_unit := c.multiplicationOver_unit_right φ
  norm_unit := c.normOver_unit φ
  norm_mul := c.normOver_mul φ
  polar_nondegenerate := (c.normOver_nondegenerate φ).1

end Langlands.GroupScheme.CayleyDatum
