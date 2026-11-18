import Langlands.GroupScheme.Composition.CayleyAutomorphismGroup

/-! # Torus and root-group automorphisms of Zorn's split Cayley algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitCayley

/-- The twelve roots of the diagonal torus acting on Zorn's algebra. Coordinates are
`(a, u₁, u₂, u₃, v₁, v₂, v₃, b)`; the torus weights of `uᵢ` and `vᵢ` are `eᵢ` and `-eᵢ`, with
`e₁ + e₂ + e₃ = 0`. The short roots are `uᵢ = eᵢ` and `vᵢ = -eᵢ`; the long root `lᵢⱼ` is
`eᵢ - eⱼ`. -/
inductive Root
  | u1 | u2 | u3 | v1 | v2 | v3 | l12 | l13 | l21 | l23 | l31 | l32
  deriving DecidableEq

section Ring

variable {A : Type u} [CommRing A]

/-- The root-group element `x_α(r)` acting on a coordinate vector. -/
def rootFun : Root → A → (Fin 8 → A) → (Fin 8 → A)
  | .u1, r, x => ![x 0 - r * x 4, x 1 + r * x 0 - r * x 7 - r ^ 2 * x 4, x 2, x 3, x 4,
      x 5 - r * x 3, x 6 + r * x 2, x 7 + r * x 4]
  | .u2, r, x => ![x 0 - r * x 5, x 1, x 2 + r * x 0 - r * x 7 - r ^ 2 * x 5, x 3,
      x 4 + r * x 3, x 5, x 6 - r * x 1, x 7 + r * x 5]
  | .u3, r, x => ![x 0 - r * x 6, x 1, x 2, x 3 + r * x 0 - r * x 7 - r ^ 2 * x 6,
      x 4 - r * x 2, x 5 + r * x 1, x 6, x 7 + r * x 6]
  | .v1, r, x => ![x 0 - r * x 1, x 1, x 2 - r * x 6, x 3 + r * x 5,
      x 4 + r * x 0 - r * x 7 - r ^ 2 * x 1, x 5, x 6, x 7 + r * x 1]
  | .v2, r, x => ![x 0 - r * x 2, x 1 + r * x 6, x 2, x 3 - r * x 4, x 4,
      x 5 + r * x 0 - r * x 7 - r ^ 2 * x 2, x 6, x 7 + r * x 2]
  | .v3, r, x => ![x 0 - r * x 3, x 1 - r * x 5, x 2 + r * x 4, x 3, x 4, x 5,
      x 6 + r * x 0 - r * x 7 - r ^ 2 * x 3, x 7 + r * x 3]
  | .l12, r, x => ![x 0, x 1 + r * x 2, x 2, x 3, x 4, x 5 - r * x 4, x 6, x 7]
  | .l13, r, x => ![x 0, x 1 + r * x 3, x 2, x 3, x 4, x 5, x 6 - r * x 4, x 7]
  | .l21, r, x => ![x 0, x 1, x 2 + r * x 1, x 3, x 4 - r * x 5, x 5, x 6, x 7]
  | .l23, r, x => ![x 0, x 1, x 2 + r * x 3, x 3, x 4, x 5, x 6 - r * x 5, x 7]
  | .l31, r, x => ![x 0, x 1, x 2, x 3 + r * x 1, x 4 - r * x 6, x 5, x 6, x 7]
  | .l32, r, x => ![x 0, x 1, x 2, x 3 + r * x 2, x 4, x 5 - r * x 6, x 6, x 7]

/-- A function on `A⁸` fixes Zorn's unit and preserves Zorn's product. -/
def IsAutomorphism (f : (Fin 8 → A) → (Fin 8 → A)) : Prop :=
  f (unit A) = unit A ∧ ∀ x y, f (mulFun A x y) = mulFun A (f x) (f y)

theorem rootFun_add (α : Root) (r : A) (x y : Fin 8 → A) :
    rootFun α r (x + y) = rootFun α r x + rootFun α r y := by
  cases α <;> funext i <;> fin_cases i <;> simp [rootFun] <;> ring

theorem rootFun_smul (α : Root) (r c : A) (x : Fin 8 → A) :
    rootFun α r (c • x) = c • rootFun α r x := by
  cases α <;> funext i <;> fin_cases i <;> simp [rootFun] <;> ring

theorem rootFun_zero (α : Root) (x : Fin 8 → A) : rootFun α 0 x = x := by
  cases α <;> funext i <;> fin_cases i <;> simp [rootFun]

theorem rootFun_rootFun (α : Root) (r s : A) (x : Fin 8 → A) :
    rootFun α r (rootFun α s x) = rootFun α (r + s) x := by
  cases α <;> funext i <;> fin_cases i <;> simp [rootFun] <;> ring

theorem rootFun_u1_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .u1 r (mulFun A x y) = mulFun A (rootFun .u1 r x) (rootFun .u1 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_u2_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .u2 r (mulFun A x y) = mulFun A (rootFun .u2 r x) (rootFun .u2 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_u3_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .u3 r (mulFun A x y) = mulFun A (rootFun .u3 r x) (rootFun .u3 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_v1_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .v1 r (mulFun A x y) = mulFun A (rootFun .v1 r x) (rootFun .v1 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_v2_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .v2 r (mulFun A x y) = mulFun A (rootFun .v2 r x) (rootFun .v2 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_v3_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .v3 r (mulFun A x y) = mulFun A (rootFun .v3 r x) (rootFun .v3 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_l12_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .l12 r (mulFun A x y) = mulFun A (rootFun .l12 r x) (rootFun .l12 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_l13_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .l13 r (mulFun A x y) = mulFun A (rootFun .l13 r x) (rootFun .l13 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_l21_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .l21 r (mulFun A x y) = mulFun A (rootFun .l21 r x) (rootFun .l21 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_l23_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .l23 r (mulFun A x y) = mulFun A (rootFun .l23 r x) (rootFun .l23 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_l31_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .l31 r (mulFun A x y) = mulFun A (rootFun .l31 r x) (rootFun .l31 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem rootFun_l32_mulFun (r : A) (x y : Fin 8 → A) :
    rootFun .l32 r (mulFun A x y) = mulFun A (rootFun .l32 r x) (rootFun .l32 r y) := by
  funext i
  fin_cases i <;> simp only [rootFun, mulFun, Matrix.cons_val, Fin.isValue] <;> ring_nf

theorem isAutomorphism_rootFun (α : Root) (r : A) : IsAutomorphism (rootFun α r) := by
  refine ⟨?_, fun x y => ?_⟩
  · cases α <;> funext i <;> fin_cases i <;> simp [rootFun, unit]
  · cases α
    · exact rootFun_u1_mulFun r x y
    · exact rootFun_u2_mulFun r x y
    · exact rootFun_u3_mulFun r x y
    · exact rootFun_v1_mulFun r x y
    · exact rootFun_v2_mulFun r x y
    · exact rootFun_v3_mulFun r x y
    · exact rootFun_l12_mulFun r x y
    · exact rootFun_l13_mulFun r x y
    · exact rootFun_l21_mulFun r x y
    · exact rootFun_l23_mulFun r x y
    · exact rootFun_l31_mulFun r x y
    · exact rootFun_l32_mulFun r x y

/-- The root-group element `x_α(r)` as an `A`-linear map. -/
def rootLin (α : Root) (r : A) : (Fin 8 → A) →ₗ[A] (Fin 8 → A) where
  toFun := rootFun α r
  map_add' := rootFun_add α r
  map_smul' c x := rootFun_smul α r c x

/-- The matrix of the root-group element `x_α(r)`. -/
def rootMatrix (α : Root) (r : A) : Matrix (Fin 8) (Fin 8) A :=
  LinearMap.toMatrix' (rootLin α r)

theorem rootMatrix_mulVec (α : Root) (r : A) (x : Fin 8 → A) :
    (rootMatrix α r).mulVec x = rootFun α r x := by
  rw [rootMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem rootMatrix_mul (α : Root) (r s : A) :
    rootMatrix α r * rootMatrix α s = rootMatrix α (r + s) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_mul]
  simp only [Matrix.toLin'_apply, LinearMap.comp_apply, rootMatrix_mulVec, rootFun_rootFun]

theorem rootMatrix_zero (α : Root) : rootMatrix α (0 : A) = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply, rootMatrix_mulVec, rootFun_zero,
    Matrix.toLin'_one, LinearMap.id_apply]

/-- The root-group element `x_α(r)` as an invertible matrix. -/
def rootGL (α : Root) (r : A) : GL (Fin 8) A where
  val := rootMatrix α r
  inv := rootMatrix α (-r)
  val_inv := by rw [rootMatrix_mul, add_neg_cancel, rootMatrix_zero]
  inv_val := by rw [rootMatrix_mul, neg_add_cancel, rootMatrix_zero]

@[simp] theorem rootGL_val (α : Root) (r : A) :
    ((rootGL α r : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A) = rootMatrix α r := rfl

theorem rootGL_add (α : Root) (r s : A) : rootGL α (r + s) = rootGL α r * rootGL α s := by
  ext : 1
  simp only [rootGL_val, Units.val_mul, rootMatrix_mul]

theorem rootGL_zero (α : Root) : rootGL α (0 : A) = 1 := by
  ext : 1
  simp only [rootGL_val, rootMatrix_zero, Units.val_one]

/-- The diagonal torus element `diag(1, s, t, s't', s', t', st, 1)`, an automorphism when
`s s' = 1` and `t t' = 1`. -/
def torusFun (s s' t t' : A) (x : Fin 8 → A) : Fin 8 → A :=
  ![x 0, s * x 1, t * x 2, s' * t' * x 3, s' * x 4, t' * x 5, s * t * x 6, x 7]

theorem isAutomorphism_torusFun {s s' t t' : A} (hs : s * s' = 1) (ht : t * t' = 1) :
    IsAutomorphism (torusFun s s' t t') := by
  refine ⟨?_, fun x y => ?_⟩
  · funext i; fin_cases i <;> simp [torusFun, unit]
  · funext i
    fin_cases i
    · simp only [torusFun, mulFun]
      simp
      linear_combination (-t * t' * x 3 * y 6 - x 1 * y 4) * hs +
        (-x 2 * y 5 - x 3 * y 6) * ht
    · simp only [torusFun, mulFun]
      simp
      linear_combination (s * (x 5 * y 6 - x 6 * y 5)) * ht
    · simp only [torusFun, mulFun]
      simp
      linear_combination (-t * (x 4 * y 6 - x 6 * y 4)) * hs
    · simp only [torusFun, mulFun]
      simp
      ring
    · simp only [torusFun, mulFun]
      simp
      linear_combination (-s' * (x 2 * y 3 - x 3 * y 2)) * ht
    · simp only [torusFun, mulFun]
      simp
      linear_combination (t' * (x 1 * y 3 - x 3 * y 1)) * hs
    · simp only [torusFun, mulFun]
      simp
      ring
    · simp only [torusFun, mulFun]
      simp
      linear_combination (-t * t' * x 6 * y 3 - x 4 * y 1) * hs +
        (-x 5 * y 2 - x 6 * y 3) * ht

/-- The diagonal entries `(1, s, t, s⁻¹t⁻¹, s⁻¹, t⁻¹, st, 1)` of the torus element with
parameters the units `s, t`. -/
def torusEntries (s t : Aˣ) : Fin 8 → Aˣ :=
  ![1, s, t, s⁻¹ * t⁻¹, s⁻¹, t⁻¹, s * t, 1]

/-- The torus element with unit parameters `s, t`, as an invertible diagonal matrix. -/
def torusGL (s t : Aˣ) : GL (Fin 8) A where
  val := Matrix.diagonal fun i => (torusEntries s t i : A)
  inv := Matrix.diagonal fun i => ((torusEntries s t i)⁻¹ : Aˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact (torusEntries s t i).mul_inv
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact (torusEntries s t i).inv_mul

theorem torusGL_val (s t : Aˣ) :
    ((torusGL s t : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A) =
      Matrix.diagonal fun i => (torusEntries s t i : A) := rfl

theorem torusGL_mulVec (s t : Aˣ) (x : Fin 8 → A) :
    ((torusGL s t : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A).mulVec x =
      torusFun (s : A) ((s⁻¹ : Aˣ) : A) (t : A) ((t⁻¹ : Aˣ) : A) x := by
  rw [torusGL_val]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> simp [torusEntries, torusFun]

theorem torusGL_mul (s t s' t' : Aˣ) :
    torusGL (s * s') (t * t') = torusGL s t * torusGL s' t' := by
  ext : 1
  rw [Units.val_mul, torusGL_val, torusGL_val, torusGL_val, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [torusEntries] <;> ring

theorem isAutomorphism_torusGL (s t : Aˣ) :
    IsAutomorphism (((torusGL s t : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A).mulVec) := by
  have h : (((torusGL s t : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A).mulVec) =
      torusFun (s : A) ((s⁻¹ : Aˣ) : A) (t : A) ((t⁻¹ : Aˣ) : A) :=
    funext (torusGL_mulVec s t)
  rw [h]
  exact isAutomorphism_torusFun s.mul_inv t.mul_inv

theorem isAutomorphism_rootGL (α : Root) (r : A) :
    IsAutomorphism (((rootGL α r : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A).mulVec) := by
  have h : (((rootGL α r : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A).mulVec) = rootFun α r :=
    funext (rootMatrix_mulVec α r)
  rw [h]
  exact isAutomorphism_rootFun α r

end Ring

end SplitCayley

end Langlands.GroupScheme
