import Langlands.Automorphic.CuspidalWhittaker.ArchimedeanFunctional
import Langlands.Automorphic.CuspidalArchimedeanPlaceComponent
import Langlands.Global.AdelicGLStandardCompact
import Langlands.Global.ArchimedeanPlaceCompact
import Langlands.Global.ArchimedeanPlaceLie

/-!
# Whittaker functionals on place-stable subspaces of cuspidal realizations

This module proves `CuspidalArchimedeanWhittakerFunctionalStatement`: every nonzero subspace
of a cuspidal operator realization of `GL_{r+1}` that is stable under the compact and Lie
actions at an infinite place `v` carries a Whittaker functional, nonzero on it, for some
nondegenerate character.

The functional is `ℓ_h : x ↦ W_x(h)` (`realizationFunctional`) for a point `h` whose
`v`-component `B` is upper triangular. For the matrix unit `X = E_{pq}` (`p < q`) at `v`, the
Lie derivative formula of `ArchimedeanFunctional` gives
`ℓ_h (X · x) = 2π i · Tr(∑ᵢ (B X B⁻¹)_{i,i+1}) · ℓ_h x`, and the superdiagonal of `B E_{pq} B⁻¹`
is `δ_{q,p+1} B_{pp} (B⁻¹)_{p+1,p+1} E_{p,p+1}`. Summing over matrix units gives the
Whittaker identity with `aₚ = 2π B_{pp} (B⁻¹)_{p+1,p+1}` at a real place and
`aₚ = 4π B_{pp} (B⁻¹)_{p+1,p+1}` at a complex place. To make `ℓ_h` nonzero on the subspace,
take `x₀` in it and `g₀` with `W_{x₀}(g₀) ≠ 0`, write the `v`-component of `g₀` as `b k` with `b`
upper triangular and `k` orthogonal or unitary, and use `h = g₀ k⁻¹` and the vector `k · x₀`.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.CuspidalWhittaker

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Matrix units conjugated by upper triangular matrices -/

section MatrixUnits

variable {R : Type*} [CommRing R] {n : ℕ}

theorem mul_single_mul_apply (B B' : Matrix (Fin n) (Fin n) R) (p q i j : Fin n) (c : R) :
    (B * Matrix.single p q c * B') i j = B i p * c * B' q j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

/-- Conjugating a matrix unit above the diagonal by upper triangular matrices gives a
strictly upper triangular matrix. -/
theorem conj_single_apply_eq_zero {B B' : Matrix (Fin n) (Fin n) R}
    (hB : B.IsUpperTriangular) (hB' : B'.IsUpperTriangular) {p q : Fin n} (hpq : p < q)
    (c : R) {i j : Fin n} (hji : (j : ℕ) ≤ i) : (B * Matrix.single p q c * B') i j = 0 := by
  rw [mul_single_mul_apply]
  by_cases hip : p < i
  · rw [hB hip, zero_mul, zero_mul]
  · by_cases hqj : j < q
    · rw [hB' hqj, mul_zero]
    · exfalso
      rw [not_lt, Fin.le_def] at hip hqj
      rw [Fin.lt_def] at hpq
      omega

theorem conj_single_superdiag_eq_zero {r : ℕ} {B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (hB : B.IsUpperTriangular) (hB' : B'.IsUpperTriangular) {p q : Fin (r + 1)}
    (hpq : p < q) (c : R) (i : Fin r) (h : ¬((i : ℕ) = p ∧ (q : ℕ) = p + 1)) :
    B i.castSucc p * c * B' q i.succ = 0 := by
  by_cases hip : p < i.castSucc
  · rw [show B i.castSucc p = 0 from hB hip, zero_mul, zero_mul]
  · by_cases hqi : i.succ < q
    · rw [show B' q i.succ = 0 from hB' hqi, mul_zero]
    · exfalso
      apply h
      rw [not_lt, Fin.le_def, Fin.val_castSucc] at hip
      rw [not_lt, Fin.le_def, Fin.val_succ] at hqi
      rw [Fin.lt_def] at hpq
      omega

/-- The superdiagonal sum of a conjugated matrix unit above the diagonal. -/
theorem sum_superdiag_conj_single {r : ℕ} {B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (hB : B.IsUpperTriangular) (hB' : B'.IsUpperTriangular) {p q : Fin (r + 1)} (hpq : p < q)
    (c : R) :
    ∑ i : Fin r, (B * Matrix.single p q c * B') i.castSucc i.succ =
      if (q : ℕ) = p + 1 then B p p * c * B' q q else 0 := by
  simp_rw [mul_single_mul_apply]
  split_ifs with hq
  · have hp : (p : ℕ) < r := by
      have := q.isLt
      omega
    rw [Finset.sum_eq_single_of_mem (⟨p, hp⟩ : Fin r) (Finset.mem_univ _) fun i _ hi =>
      conj_single_superdiag_eq_zero hB hB' hpq c i fun h => hi (Fin.ext h.1)]
    have h1 : (⟨p, hp⟩ : Fin r).castSucc = p := Fin.ext rfl
    have h2 : (⟨p, hp⟩ : Fin r).succ = q := Fin.ext (by simp [hq])
    rw [h1, h2]
  · exact Finset.sum_eq_zero fun i _ =>
      conj_single_superdiag_eq_zero hB hB' hpq c i fun h => hq h.2

/-- Diagonal entries of mutually inverse upper triangular matrices multiply to one. -/
theorem diag_mul_diag_eq_one {B B' : Matrix (Fin n) (Fin n) R} (hB : B.IsUpperTriangular)
    (hB' : B'.IsUpperTriangular) (h : B * B' = 1) (p : Fin n) : B p p * B' p p = 1 := by
  have h1 := congrFun (congrFun h p) p
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single p] at h1
  · exact h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hB hk, zero_mul]
    · rw [hB' hk, mul_zero]
  · simp

/-- A right inverse of an upper triangular matrix is upper triangular. -/
theorem isUpperTriangular_of_mul_eq_one {B B' : Matrix (Fin n) (Fin n) R}
    (hB : B.IsUpperTriangular) (h : B * B' = 1) : B'.IsUpperTriangular := by
  let := invertibleOfRightInverse B B' h
  rw [← Matrix.inv_eq_right_inv h]
  exact Matrix.blockTriangular_inv_of_blockTriangular hB

/-- The superdiagonal double sum of the Whittaker identity on a matrix unit. -/
theorem sum_sum_superdiag_single (a : Fin n → R) (p q : Fin n) (c : R) :
    (∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = i + 1 then a i * Matrix.single p q c i j else 0) =
      if (q : ℕ) = p + 1 then a p * c else 0 := by
  have hrow : ∀ i : Fin n, i ≠ p →
      (∑ j : Fin n, if (j : ℕ) = i + 1 then a i * Matrix.single p q c i j else 0) = 0 := by
    intro i hi
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply_of_row_ne (Ne.symm hi), mul_zero, ite_self]
  rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ p) fun i _ hi => hrow i hi,
    Finset.sum_eq_single_of_mem q (Finset.mem_univ q) fun j _ hj => by
      rw [Matrix.single_apply_of_ne p q c p j (fun h => hj h.2.symm), mul_zero, ite_self],
    Matrix.single_apply_same]

end MatrixUnits

/-! ### Whittaker identities from matrix units -/

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- A functional satisfying the real Whittaker identity on every matrix unit above the
diagonal is a real Whittaker functional. -/
theorem isRealWhittakerFunctional_of_single
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ V) (a : Fin n → ℝ) (ℓ : V →ₗ[ℂ] ℂ)
    (h : ∀ p q : Fin n, p < q → ∀ (c : ℝ), ∀ x ∈ W,
      ℓ (π (1 ⊗ₜ Matrix.single p q c) x) =
        Complex.I * ((if (q : ℕ) = p + 1 then a p * c else 0 : ℝ) : ℂ) * ℓ x) :
    PlaceComponent.IsRealWhittakerFunctional π W a ℓ := by
  intro X hX x hx
  have hterm : ∀ p q : Fin n, ℓ (π (1 ⊗ₜ Matrix.single p q (X p q)) x) =
      Complex.I * ((if (q : ℕ) = p + 1 then a p * X p q else 0 : ℝ) : ℂ) * ℓ x := by
    intro p q
    by_cases hpq : p < q
    · exact h p q hpq (X p q) x hx
    · rw [not_lt, Fin.le_def] at hpq
      have hne : ¬(q : ℕ) = p + 1 := by omega
      rw [hX p q hpq, Matrix.single_zero, TensorProduct.tmul_zero, map_zero,
        LinearMap.zero_apply, map_zero, ite_eq_right hne, Complex.ofReal_zero, mul_zero, zero_mul]
  calc ℓ (π (1 ⊗ₜ X) x)
      = ∑ p : Fin n, ∑ q : Fin n, ℓ (π (1 ⊗ₜ Matrix.single p q (X p q)) x) := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single X]
        simp only [TensorProduct.tmul_sum, map_sum, LinearMap.sum_apply]
    _ = _ := by
        simp only [hterm, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]

/-- A functional satisfying the complex Whittaker identity on every matrix unit above the
diagonal is a complex Whittaker functional. -/
theorem isComplexWhittakerFunctional_of_single
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ V) (a : Fin n → ℂ) (ℓ : V →ₗ[ℂ] ℂ)
    (h : ∀ p q : Fin n, p < q → ∀ (c : ℂ), ∀ x ∈ W,
      ℓ (π (1 ⊗ₜ Matrix.single p q c) x) =
        Complex.I * (((if (q : ℕ) = p + 1 then a p * c else 0 : ℂ).re : ℝ) : ℂ) * ℓ x) :
    PlaceComponent.IsComplexWhittakerFunctional π W a ℓ := by
  intro X hX x hx
  have hterm : ∀ p q : Fin n, ℓ (π (1 ⊗ₜ Matrix.single p q (X p q)) x) =
      Complex.I * (((if (q : ℕ) = p + 1 then a p * X p q else 0 : ℂ).re : ℝ) : ℂ) * ℓ x := by
    intro p q
    by_cases hpq : p < q
    · exact h p q hpq (X p q) x hx
    · rw [not_lt, Fin.le_def] at hpq
      have hne : ¬(q : ℕ) = p + 1 := by omega
      rw [hX p q hpq, Matrix.single_zero, TensorProduct.tmul_zero, map_zero,
        LinearMap.zero_apply, map_zero, ite_eq_right hne, Complex.zero_re, Complex.ofReal_zero,
        mul_zero, zero_mul]
  calc ℓ (π (1 ⊗ₜ X) x)
      = ∑ p : Fin n, ∑ q : Fin n, ℓ (π (1 ⊗ₜ Matrix.single p q (X p q)) x) := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single X]
        simp only [TensorProduct.tmul_sum, map_sum, LinearMap.sum_apply]
    _ = _ := by
        simp only [hterm, Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]

end Abstract

/-! ### Place coordinates of conjugated directions -/

section Coordinates

open Langlands.Global Langlands.Global.PrimitiveAdelicHeight

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- The matrix at the place `φ` of the archimedean component of `h`. -/
def placeMatrix {𝕜 : Type*} [CommRing 𝕜]
    (φ : NumberField.mixedEmbedding.mixedSpace F →+* 𝕜) (h : AdelicGL F n) :
    Matrix.GeneralLinearGroup (Fin n) 𝕜 :=
  Matrix.GeneralLinearGroup.map φ (archimedeanGLCoordinates F n (AdelicGL.infinite F n h))

theorem placeMatrix_mul_inv {𝕜 : Type*} [CommRing 𝕜]
    (φ : NumberField.mixedEmbedding.mixedSpace F →+* 𝕜) (h : AdelicGL F n) :
    (placeMatrix φ h).val * ((placeMatrix φ h)⁻¹).val = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem mapMatrix_conjDirection {𝕜 : Type*} [CommRing 𝕜]
    (φ : NumberField.mixedEmbedding.mixedSpace F →+* 𝕜) (h : AdelicGL F n)
    (Y : ArchimedeanGL.RealLieAlgebra F n) :
    φ.mapMatrix (conjDirection h Y) = (placeMatrix φ h).val *
      φ.mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n Y) *
        ((placeMatrix φ h)⁻¹).val := by
  rw [conjDirection, map_mul, map_mul]
  rfl

omit [NumberField F] in
theorem realCoord_mapMatrix_realPlaceLieInclusion_self (v : RP)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    (realCoord v).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
      (ArchimedeanGL.realPlaceLieInclusion F n v X)) = X := by
  have h := ArchimedeanGL.realProjection_realInclusion F n v v X
  rw [Pi.single_eq_same] at h
  ext i j
  exact congrFun (congrFun h i) j

omit [NumberField F] in
theorem realCoord_mapMatrix_realPlaceLieInclusion_of_ne {v w : RP} (hwv : w ≠ v)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    (realCoord w).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
      (ArchimedeanGL.realPlaceLieInclusion F n v X)) = 0 := by
  have h := ArchimedeanGL.realProjection_realInclusion F n w v X
  rw [Pi.single_eq_of_ne hwv] at h
  ext i j
  exact congrFun (congrFun h i) j

omit [NumberField F] in
theorem complexCoord_mapMatrix_realPlaceLieInclusion (v : RP) (w : CP)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    (complexCoord w).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
      (ArchimedeanGL.realPlaceLieInclusion F n v X)) = 0 := by
  have h := ArchimedeanGL.complexProjection_realInclusion F n w v X
  ext i j
  exact congrFun (congrFun h i) j

omit [NumberField F] in
theorem complexCoord_mapMatrix_complexPlaceLieInclusion_self (v : CP)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (complexCoord v).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
      (ArchimedeanGL.complexPlaceLieInclusion F n v X)) = X := by
  have h := ArchimedeanGL.complexProjection_complexInclusion F n v v X
  rw [Pi.single_eq_same] at h
  ext i j
  exact congrFun (congrFun h i) j

omit [NumberField F] in
theorem complexCoord_mapMatrix_complexPlaceLieInclusion_of_ne {v w : CP} (hwv : w ≠ v)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (complexCoord w).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
      (ArchimedeanGL.complexPlaceLieInclusion F n v X)) = 0 := by
  have h := ArchimedeanGL.complexProjection_complexInclusion F n w v X
  rw [Pi.single_eq_of_ne hwv] at h
  ext i j
  exact congrFun (congrFun h i) j

omit [NumberField F] in
theorem realCoord_mapMatrix_complexPlaceLieInclusion (v : CP) (w : RP)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (realCoord w).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
      (ArchimedeanGL.complexPlaceLieInclusion F n v X)) = 0 := by
  have h := ArchimedeanGL.realProjection_complexInclusion F n w v X
  ext i j
  exact congrFun (congrFun h i) j

omit [NumberField F] in
/-- Archimedean matrices are determined by their matrices at all infinite places. -/
theorem archimedeanMatrix_ext {Z Z' : ArchimedeanMatrix F n}
    (hr : ∀ w : RP, (realCoord w).mapMatrix Z = (realCoord w).mapMatrix Z')
    (hc : ∀ w : CP, (complexCoord w).mapMatrix Z = (complexCoord w).mapMatrix Z') :
    Z = Z' :=
  Matrix.ext fun i j => Prod.ext (funext fun w => congrFun (congrFun (hr w) i) j)
    (funext fun w => congrFun (congrFun (hc w) i) j)

/-- The direction of a real-place matrix, conjugated by the archimedean component of `h`,
has entries `B X B⁻¹` at `v` and zero elsewhere. -/
theorem conjDirection_realPlace_apply (h : AdelicGL F n) (v : RP)
    (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    conjDirection h (ArchimedeanGL.realPlaceLieInclusion F n v X) i j =
      (Pi.single v (((placeMatrix (realCoord v) h).val * X *
        ((placeMatrix (realCoord v) h)⁻¹).val) i j), 0) := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have hw : realCoord w (conjDirection h (ArchimedeanGL.realPlaceLieInclusion F n v X) i j) =
        ((placeMatrix (realCoord w) h).val *
          (realCoord w).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
            (ArchimedeanGL.realPlaceLieInclusion F n v X)) *
          ((placeMatrix (realCoord w) h)⁻¹).val) i j :=
      congrFun (congrFun (mapMatrix_conjDirection (realCoord w) h _) i) j
    dsimp only
    change realCoord w _ = _
    rcases eq_or_ne w v with rfl | hwv
    · rw [realCoord_mapMatrix_realPlaceLieInclusion_self] at hw
      rw [hw, Pi.single_eq_same]
    · rw [realCoord_mapMatrix_realPlaceLieInclusion_of_ne hwv, Matrix.mul_zero,
        Matrix.zero_mul] at hw
      rw [hw, Pi.single_eq_of_ne hwv, Matrix.zero_apply]
  · have hw : complexCoord w
        (conjDirection h (ArchimedeanGL.realPlaceLieInclusion F n v X) i j) =
        ((placeMatrix (complexCoord w) h).val *
          (complexCoord w).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
            (ArchimedeanGL.realPlaceLieInclusion F n v X)) *
          ((placeMatrix (complexCoord w) h)⁻¹).val) i j :=
      congrFun (congrFun (mapMatrix_conjDirection (complexCoord w) h _) i) j
    dsimp only
    change complexCoord w _ = _
    rw [complexCoord_mapMatrix_realPlaceLieInclusion, Matrix.mul_zero, Matrix.zero_mul] at hw
    rw [hw, Matrix.zero_apply, Pi.zero_apply]

/-- The direction of a complex-place matrix, conjugated by the archimedean component of
`h`, has entries `B X B⁻¹` at `v` and zero elsewhere. -/
theorem conjDirection_complexPlace_apply (h : AdelicGL F n) (v : CP)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    conjDirection h (ArchimedeanGL.complexPlaceLieInclusion F n v X) i j =
      (0, Pi.single v (((placeMatrix (complexCoord v) h).val * X *
        ((placeMatrix (complexCoord v) h)⁻¹).val) i j)) := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have hw : realCoord w
        (conjDirection h (ArchimedeanGL.complexPlaceLieInclusion F n v X) i j) =
        ((placeMatrix (realCoord w) h).val *
          (realCoord w).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
            (ArchimedeanGL.complexPlaceLieInclusion F n v X)) *
          ((placeMatrix (realCoord w) h)⁻¹).val) i j :=
      congrFun (congrFun (mapMatrix_conjDirection (realCoord w) h _) i) j
    dsimp only
    change realCoord w _ = _
    rw [realCoord_mapMatrix_complexPlaceLieInclusion, Matrix.mul_zero, Matrix.zero_mul] at hw
    rw [hw, Matrix.zero_apply, Pi.zero_apply]
  · have hw : complexCoord w
        (conjDirection h (ArchimedeanGL.complexPlaceLieInclusion F n v X) i j) =
        ((placeMatrix (complexCoord w) h).val *
          (complexCoord w).mapMatrix (ArchimedeanGL.realLieAlgebraToMatrix F n
            (ArchimedeanGL.complexPlaceLieInclusion F n v X)) *
          ((placeMatrix (complexCoord w) h)⁻¹).val) i j :=
      congrFun (congrFun (mapMatrix_conjDirection (complexCoord w) h _) i) j
    dsimp only
    change complexCoord w _ = _
    rcases eq_or_ne w v with rfl | hwv
    · rw [complexCoord_mapMatrix_complexPlaceLieInclusion_self] at hw
      rw [hw, Pi.single_eq_same]
    · rw [complexCoord_mapMatrix_complexPlaceLieInclusion_of_ne hwv, Matrix.mul_zero,
        Matrix.zero_mul] at hw
      rw [hw, Pi.single_eq_of_ne hwv, Matrix.zero_apply]

omit [NumberField F] in
/-- A real-place direction with square-zero matrix has square-zero archimedean matrix. -/
theorem realLieAlgebraToMatrix_realPlace_mul_self (v : RP) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X * X = 0) :
    ArchimedeanGL.realLieAlgebraToMatrix F n (ArchimedeanGL.realPlaceLieInclusion F n v X) *
      ArchimedeanGL.realLieAlgebraToMatrix F n
        (ArchimedeanGL.realPlaceLieInclusion F n v X) = 0 := by
  refine archimedeanMatrix_ext (fun w => ?_) (fun w => ?_)
  · rw [map_mul, map_zero]
    rcases eq_or_ne w v with rfl | hwv
    · rw [realCoord_mapMatrix_realPlaceLieInclusion_self, hX]
    · rw [realCoord_mapMatrix_realPlaceLieInclusion_of_ne hwv, mul_zero]
  · rw [map_mul, map_zero, complexCoord_mapMatrix_realPlaceLieInclusion, mul_zero]

omit [NumberField F] in
/-- A complex-place direction with square-zero matrix has square-zero archimedean matrix. -/
theorem realLieAlgebraToMatrix_complexPlace_mul_self (v : CP) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X * X = 0) :
    ArchimedeanGL.realLieAlgebraToMatrix F n (ArchimedeanGL.complexPlaceLieInclusion F n v X) *
      ArchimedeanGL.realLieAlgebraToMatrix F n
        (ArchimedeanGL.complexPlaceLieInclusion F n v X) = 0 := by
  refine archimedeanMatrix_ext (fun w => ?_) (fun w => ?_)
  · rw [map_mul, map_zero, realCoord_mapMatrix_complexPlaceLieInclusion, mul_zero]
  · rw [map_mul, map_zero]
    rcases eq_or_ne w v with rfl | hwv
    · rw [complexCoord_mapMatrix_complexPlaceLieInclusion_self, hX]
    · rw [complexCoord_mapMatrix_complexPlaceLieInclusion_of_ne hwv, mul_zero]

/-- The coefficients of the real-place character: `aₚ = 2π B_{pp} (B⁻¹)_{p+1,p+1}` for the
`v`-component `B` of the archimedean component of `h` (and `1` for the last index, which no
superdiagonal entry uses). -/
def realWhittakerCoeff {r : ℕ} (h : AdelicGL F (r + 1)) (v : RP) (p : Fin (r + 1)) : ℝ :=
  if hp : (p : ℕ) + 1 < r + 1 then
    2 * Real.pi * ((placeMatrix (realCoord v) h).val p p *
      ((placeMatrix (realCoord v) h)⁻¹).val ⟨p + 1, hp⟩ ⟨p + 1, hp⟩)
  else 1

/-- The coefficients of the complex-place character: `aₚ = 4π B_{pp} (B⁻¹)_{p+1,p+1}` for
the `v`-component `B` of the archimedean component of `h` (and `1` for the last index). -/
def complexWhittakerCoeff {r : ℕ} (h : AdelicGL F (r + 1)) (v : CP) (p : Fin (r + 1)) : ℂ :=
  if hp : (p : ℕ) + 1 < r + 1 then
    4 * (Real.pi : ℂ) * ((placeMatrix (complexCoord v) h).val p p *
      ((placeMatrix (complexCoord v) h)⁻¹).val ⟨p + 1, hp⟩ ⟨p + 1, hp⟩)
  else 1

/-- The mixed trace of the superdiagonal of a conjugated real-place direction. -/
theorem mixedTrace_conjDirection_realPlace {r : ℕ} (h : AdelicGL F (r + 1)) (v : RP)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :
    mixedTrace F (∑ i : Fin r,
      conjDirection h (ArchimedeanGL.realPlaceLieInclusion F (r + 1) v X) i.castSucc i.succ) =
      ∑ i : Fin r, ((placeMatrix (realCoord v) h).val * X *
        ((placeMatrix (realCoord v) h)⁻¹).val) i.castSucc i.succ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjDirection_realPlace_apply, mixedTrace_single_real]

/-- The mixed trace of the superdiagonal of a conjugated complex-place direction. -/
theorem mixedTrace_conjDirection_complexPlace {r : ℕ} (h : AdelicGL F (r + 1)) (v : CP)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    mixedTrace F (∑ i : Fin r,
      conjDirection h (ArchimedeanGL.complexPlaceLieInclusion F (r + 1) v X) i.castSucc
        i.succ) =
      2 * (∑ i : Fin r, ((placeMatrix (complexCoord v) h).val * X *
        ((placeMatrix (complexCoord v) h)⁻¹).val) i.castSucc i.succ).re := by
  rw [map_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjDirection_complexPlace_apply, mixedTrace_single_complex]

theorem two_pi_mul_realSuperdiag {r : ℕ} (h : AdelicGL F (r + 1)) (v : RP)
    (p q : Fin (r + 1)) (c : ℝ) :
    2 * Real.pi * (if (q : ℕ) = p + 1 then (placeMatrix (realCoord v) h).val p p * c *
      ((placeMatrix (realCoord v) h)⁻¹).val q q else 0) =
      if (q : ℕ) = p + 1 then realWhittakerCoeff h v p * c else 0 := by
  split_ifs with hq
  · have hp : (p : ℕ) + 1 < r + 1 := by
      have := q.isLt
      omega
    have hq' : (⟨p + 1, hp⟩ : Fin (r + 1)) = q := Fin.ext hq.symm
    rw [realWhittakerCoeff, dite_eq_left_of_eq_true (eq_true hp), hq']
    ring
  · ring

theorem two_pi_mul_complexSuperdiag {r : ℕ} (h : AdelicGL F (r + 1)) (v : CP)
    (p q : Fin (r + 1)) (c : ℂ) :
    2 * Real.pi * (2 * (if (q : ℕ) = p + 1 then (placeMatrix (complexCoord v) h).val p p * c *
      ((placeMatrix (complexCoord v) h)⁻¹).val q q else 0).re) =
      (if (q : ℕ) = p + 1 then complexWhittakerCoeff h v p * c else 0).re := by
  split_ifs with hq
  · have hp : (p : ℕ) + 1 < r + 1 := by
      have := q.isLt
      omega
    have hq' : (⟨p + 1, hp⟩ : Fin (r + 1)) = q := Fin.ext hq.symm
    rw [complexWhittakerCoeff, dite_eq_left_of_eq_true (eq_true hp), hq']
    have hc : 4 * (Real.pi : ℂ) * ((placeMatrix (complexCoord v) h).val p p *
        ((placeMatrix (complexCoord v) h)⁻¹).val q q) * c =
        ((4 * Real.pi : ℝ) : ℂ) * ((placeMatrix (complexCoord v) h).val p p * c *
          ((placeMatrix (complexCoord v) h)⁻¹).val q q) := by
      push_cast
      ring
    rw [hc, Complex.re_ofReal_mul]
    ring
  · simp

end Coordinates

/-! ### The functional on matrix units at one place -/

section Realization

open Langlands.Global Langlands.Global.PrimitiveAdelicHeight
  Langlands.Automorphic.ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance placeWhittakerRationalAddCommGroup {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeWhittakerContinuousAddCommGroup {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeWhittakerSmoothAddCommGroup {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeWhittakerFormsAddCommGroup {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeWhittakerStableAddCommGroup {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance placeWhittakerSpaceAddCommGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (S : OperatorRealization F (r + 1))

/-- The real Whittaker identity of `ℓ_h` on a matrix unit above the diagonal at a real
place `v`, when the `v`-component of `h` is upper triangular. -/
theorem realizationFunctional_realPlaceLieAction_single (hS : S.IsCuspidal)
    (h : AdelicGL F (r + 1)) (v : RP)
    (hB : (placeMatrix (realCoord v) h).val.IsUpperTriangular) {p q : Fin (r + 1)}
    (hpq : p < q) (c : ℝ) (x : S.Space) :
    realizationFunctional S hS h (S.realPlaceLieAction v (1 ⊗ₜ Matrix.single p q c) x) =
      Complex.I * ((if (q : ℕ) = p + 1 then realWhittakerCoeff h v p * c else 0 : ℝ) : ℂ) *
        realizationFunctional S hS h x := by
  have hB' := isUpperTriangular_of_mul_eq_one hB (placeMatrix_mul_inv (realCoord v) h)
  have hlie : S.realPlaceLieAction v (1 ⊗ₜ Matrix.single p q c) x =
      S.lieOperator (ArchimedeanGL.realPlaceLieInclusion F (r + 1) v (Matrix.single p q c)) x :=
    rfl
  have hsq : Matrix.single p q c * Matrix.single p q c = 0 :=
    Matrix.single_mul_single_of_ne c p q p (ne_of_gt hpq) c
  have hY := realLieAlgebraToMatrix_realPlace_mul_self (F := F) v hsq
  have hN : ∀ i j : Fin (r + 1), (j : ℕ) ≤ i → conjDirection h
      (ArchimedeanGL.realPlaceLieInclusion F (r + 1) v (Matrix.single p q c)) i j = 0 := by
    intro i j hji
    rw [conjDirection_realPlace_apply, conj_single_apply_eq_zero hB hB' hpq c hji,
      Pi.single_zero, Prod.mk_zero_zero]
  have hτ : 2 * Real.pi * mixedTrace F (∑ i : Fin r, conjDirection h
      (ArchimedeanGL.realPlaceLieInclusion F (r + 1) v (Matrix.single p q c)) i.castSucc
        i.succ) = if (q : ℕ) = p + 1 then realWhittakerCoeff h v p * c else 0 := by
    rw [mixedTrace_conjDirection_realPlace h v (Matrix.single p q c),
      sum_superdiag_conj_single hB hB' hpq c, two_pi_mul_realSuperdiag h v p q c]
  rw [hlie, realizationFunctional_lieOperator S hS h _ hY hN x]
  exact (congrArg (fun t : ℝ => ((t : ℂ) * Complex.I) * realizationFunctional S hS h x) hτ).trans
    (congrArg (fun z => z * realizationFunctional S hS h x) (mul_comm _ _))

/-- The complex Whittaker identity of `ℓ_h` on a matrix unit above the diagonal at a
complex place `v`, when the `v`-component of `h` is upper triangular. -/
theorem realizationFunctional_complexPlaceLieAction_single (hS : S.IsCuspidal)
    (h : AdelicGL F (r + 1)) (v : CP)
    (hB : (placeMatrix (complexCoord v) h).val.IsUpperTriangular) {p q : Fin (r + 1)}
    (hpq : p < q) (c : ℂ) (x : S.Space) :
    realizationFunctional S hS h (S.complexPlaceLieAction v (1 ⊗ₜ Matrix.single p q c) x) =
      Complex.I *
        (((if (q : ℕ) = p + 1 then complexWhittakerCoeff h v p * c else 0 : ℂ).re : ℝ) : ℂ) *
        realizationFunctional S hS h x := by
  have hB' := isUpperTriangular_of_mul_eq_one hB (placeMatrix_mul_inv (complexCoord v) h)
  have hlie : S.complexPlaceLieAction v (1 ⊗ₜ Matrix.single p q c) x =
      S.lieOperator
        (ArchimedeanGL.complexPlaceLieInclusion F (r + 1) v (Matrix.single p q c)) x :=
    rfl
  have hsq : Matrix.single p q c * Matrix.single p q c = 0 :=
    Matrix.single_mul_single_of_ne c p q p (ne_of_gt hpq) c
  have hY := realLieAlgebraToMatrix_complexPlace_mul_self (F := F) v hsq
  have hN : ∀ i j : Fin (r + 1), (j : ℕ) ≤ i → conjDirection h
      (ArchimedeanGL.complexPlaceLieInclusion F (r + 1) v (Matrix.single p q c)) i j = 0 := by
    intro i j hji
    rw [conjDirection_complexPlace_apply, conj_single_apply_eq_zero hB hB' hpq c hji,
      Pi.single_zero, Prod.mk_zero_zero]
  have hτ : 2 * Real.pi * mixedTrace F (∑ i : Fin r, conjDirection h
      (ArchimedeanGL.complexPlaceLieInclusion F (r + 1) v (Matrix.single p q c)) i.castSucc
        i.succ) = (if (q : ℕ) = p + 1 then complexWhittakerCoeff h v p * c else 0).re := by
    rw [mixedTrace_conjDirection_complexPlace h v (Matrix.single p q c),
      sum_superdiag_conj_single hB hB' hpq c, two_pi_mul_complexSuperdiag h v p q c]
  rw [hlie, realizationFunctional_lieOperator S hS h _ hY hN x]
  exact (congrArg (fun t : ℝ => ((t : ℂ) * Complex.I) * realizationFunctional S hS h x) hτ).trans
    (congrArg (fun z => z * realizationFunctional S hS h x) (mul_comm _ _))

omit [CompactSpace (AdeleQuotient F)] in
/-- A nonzero vector of an operator realization has a nonzero realized value. -/
theorem operatorRealization_exists_evaluate_ne_zero {x : S.Space} (hx : x ≠ 0) :
    ∃ g, evaluate F (r + 1) (S.toContinuous x) g ≠ 0 := by
  by_contra h'
  have h : ∀ g, evaluate F (r + 1) (S.toContinuous x) g = 0 := fun g => by
    by_contra hg
    exact h' ⟨g, hg⟩
  apply hx
  apply S.toContinuous_injective
  rw [map_zero S.toContinuous]
  apply toContinuousMap_injective F (r + 1)
  rw [map_zero (toContinuousMap F (r + 1))]
  ext g
  exact h g

/-- If `x'` is the right translate of `x` by `c`, then `ℓ_{g c⁻¹}(x') = W_x(g)`. -/
theorem realizationFunctional_translate (hS : S.IsCuspidal) {x x' : S.Space}
    {c : AdelicGL F (r + 1)}
    (hx' : ∀ a, evaluate F (r + 1) (S.toContinuous x') a =
      evaluate F (r + 1) (S.toContinuous x) (a * c)) (g : AdelicGL F (r + 1)) :
    realizationFunctional S hS (g * c⁻¹) x' = descend r (evaluate F (r + 1) (S.toContinuous x)) g := by
  rw [realizationFunctional_apply, show evaluate F (r + 1) (S.toContinuous x') =
      fun a => evaluate F (r + 1) (S.toContinuous x) (a * c) from funext hx',
    descend_mul_right]
  exact congrArg _ (inv_mul_cancel_right g c)

/-- **Real places.** Every nonzero place-stable subspace of a cuspidal realization at a real
place carries a real Whittaker functional, nonzero on it, for a nondegenerate character. -/
theorem isRealGeneric_of_isStable (hS : S.IsCuspidal) (v : RP) (W : Submodule ℂ S.Space)
    (hW : W ≠ ⊥)
    (hstab : PlaceComponent.IsStable (S.realPlaceCompactRepresentation v)
      (S.realPlaceLieAction v) W) :
    PlaceComponent.IsRealGeneric (S.realPlaceLieAction v) W := by
  obtain ⟨x0, hx0W, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨g0, hg0⟩ := exists_descend_ne_zero r le_rfl _ (levelProps_realization S hS x0)
    (operatorRealization_exists_evaluate_ne_zero S hx0)
  obtain ⟨b, u, hf⟩ := Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary
    (Matrix.GeneralLinearGroup.map (realCoord v)
      (archimedeanGLCoordinates F (r + 1) (AdelicGL.infinite F (r + 1) g0))).val (Units.isUnit _)
  obtain ⟨k, hk⟩ : ∃ k : Matrix.unitaryGroup (Fin (r + 1)) ℝ,
      (k : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) = u := ⟨⟨u, hf.2.2.1⟩, rfl⟩
  obtain ⟨h0, hh0⟩ : ∃ h0 : AdelicGL F (r + 1), h0 = g0 *
      (AdelicGL.ofInfinite F (r + 1) (realPlaceCompactInclusion F (r + 1) v k).val)⁻¹ :=
    ⟨_, rfl⟩
  have hB : (placeMatrix (realCoord v) h0).val = b := by
    rw [hh0, placeMatrix, map_mul, map_inv, AdelicGL.infinite_ofInfinite, local_mul_inv]
    refine mul_inv_val_eq hf ?_
    have h1 := realMatrix_realPlaceCompactInclusion F (r + 1) v v k
    rw [Pi.mulSingle_eq_same] at h1
    rw [← hk]
    ext i j
    exact congrFun (congrFun h1 i) j
  have hBu : (placeMatrix (realCoord v) h0).val.IsUpperTriangular := by
    rw [hB]
    exact hf.1
  have hBinv := isUpperTriangular_of_mul_eq_one hBu (placeMatrix_mul_inv _ _)
  have hdiag := diag_mul_diag_eq_one hBu hBinv (placeMatrix_mul_inv _ _)
  refine ⟨realWhittakerCoeff h0 v, fun i hi => ?_, realizationFunctional S hS h0,
    ⟨S.realPlaceCompactRepresentation v k x0, hstab.1 k x0 hx0W, ?_⟩,
    isRealWhittakerFunctional_of_single _ _ _ _ fun p q hpq c x _ =>
      realizationFunctional_realPlaceLieAction_single S hS h0 v hBu hpq c x⟩
  · rw [realWhittakerCoeff, dite_eq_left_of_eq_true (eq_true hi)]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      (mul_ne_zero (left_ne_zero_of_mul_eq_one (hdiag i))
        (right_ne_zero_of_mul_eq_one (hdiag _)))
  · rw [hh0, realizationFunctional_translate S hS
      (fun a => S.evaluate_realPlaceCompactRepresentation v k x0 a) g0]
    exact hg0

/-- **Complex places.** Every nonzero place-stable subspace of a cuspidal realization at a
complex place carries a complex Whittaker functional, nonzero on it, for a nondegenerate
character. -/
theorem isComplexGeneric_of_isStable (hS : S.IsCuspidal) (v : CP) (W : Submodule ℂ S.Space)
    (hW : W ≠ ⊥)
    (hstab : PlaceComponent.IsStable (S.complexPlaceCompactRepresentation v)
      (S.complexPlaceLieAction v) W) :
    PlaceComponent.IsComplexGeneric (S.complexPlaceLieAction v) W := by
  obtain ⟨x0, hx0W, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨g0, hg0⟩ := exists_descend_ne_zero r le_rfl _ (levelProps_realization S hS x0)
    (operatorRealization_exists_evaluate_ne_zero S hx0)
  obtain ⟨b, u, hf⟩ := Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary
    (Matrix.GeneralLinearGroup.map (complexCoord v)
      (archimedeanGLCoordinates F (r + 1) (AdelicGL.infinite F (r + 1) g0))).val (Units.isUnit _)
  obtain ⟨k, hk⟩ : ∃ k : Matrix.unitaryGroup (Fin (r + 1)) ℂ,
      (k : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) = u := ⟨⟨u, hf.2.2.1⟩, rfl⟩
  obtain ⟨h0, hh0⟩ : ∃ h0 : AdelicGL F (r + 1), h0 = g0 *
      (AdelicGL.ofInfinite F (r + 1) (complexPlaceCompactInclusion F (r + 1) v k).val)⁻¹ :=
    ⟨_, rfl⟩
  have hB : (placeMatrix (complexCoord v) h0).val = b := by
    rw [hh0, placeMatrix, map_mul, map_inv, AdelicGL.infinite_ofInfinite, local_mul_inv]
    refine mul_inv_val_eq hf ?_
    have h1 := complexMatrix_complexPlaceCompactInclusion F (r + 1) v v k
    rw [Pi.mulSingle_eq_same] at h1
    rw [← hk]
    ext i j
    exact congrFun (congrFun h1 i) j
  have hBu : (placeMatrix (complexCoord v) h0).val.IsUpperTriangular := by
    rw [hB]
    exact hf.1
  have hBinv := isUpperTriangular_of_mul_eq_one hBu (placeMatrix_mul_inv _ _)
  have hdiag := diag_mul_diag_eq_one hBu hBinv (placeMatrix_mul_inv _ _)
  refine ⟨complexWhittakerCoeff h0 v, fun i hi => ?_, realizationFunctional S hS h0,
    ⟨S.complexPlaceCompactRepresentation v k x0, hstab.1 k x0 hx0W, ?_⟩,
    isComplexWhittakerFunctional_of_single _ _ _ _ fun p q hpq c x _ =>
      realizationFunctional_complexPlaceLieAction_single S hS h0 v hBu hpq c x⟩
  · rw [complexWhittakerCoeff, dite_eq_left_of_eq_true (eq_true hi)]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (mul_ne_zero (left_ne_zero_of_mul_eq_one (hdiag i))
        (right_ne_zero_of_mul_eq_one (hdiag _)))
  · rw [hh0, realizationFunctional_translate S hS
      (fun a => S.evaluate_complexPlaceCompactRepresentation v k x0 a) g0]
    exact hg0

end Realization

end Langlands.Automorphic.CuspidalWhittaker

namespace Langlands.Automorphic

/-- Proof of `CuspidalArchimedeanWhittakerFunctionalStatement`. -/
theorem cuspidalArchimedeanWhittakerFunctional :
    CuspidalArchimedeanWhittakerFunctionalStatement.{u} := by
  intro F _ _ _ r S hS
  exact ⟨fun v W hW hstab => CuspidalWhittaker.isRealGeneric_of_isStable S hS v W hW hstab,
    fun v W hW hstab => CuspidalWhittaker.isComplexGeneric_of_isStable S hS v W hW hstab⟩

end Langlands.Automorphic
