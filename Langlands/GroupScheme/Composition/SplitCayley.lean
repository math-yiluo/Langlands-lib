import Langlands.GroupScheme.Composition.CayleyDatum

/-! # The split Cayley datum: Zorn vector matrices over every commutative ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitCayley

section Ring

variable (R : Type u) [CommRing R]

/-- The Zorn vector-matrix product on `R⁸`, with coordinates `(a, u₁, u₂, u₃, v₁, v₂, v₃, b)`:
`(a, u, v, b) (a', u', v', b') =
  (a a' + u·v', a u' + b' u - v × v', a' v + b v' + u × u', b b' + v·u')`. -/
def mulFun (x y : Fin 8 → R) : Fin 8 → R :=
  ![x 0 * y 0 + (x 1 * y 4 + x 2 * y 5 + x 3 * y 6),
    x 0 * y 1 + y 7 * x 1 - (x 5 * y 6 - x 6 * y 5),
    x 0 * y 2 + y 7 * x 2 - (x 6 * y 4 - x 4 * y 6),
    x 0 * y 3 + y 7 * x 3 - (x 4 * y 5 - x 5 * y 4),
    y 0 * x 4 + x 7 * y 4 + (x 2 * y 3 - x 3 * y 2),
    y 0 * x 5 + x 7 * y 5 + (x 3 * y 1 - x 1 * y 3),
    y 0 * x 6 + x 7 * y 6 + (x 1 * y 2 - x 2 * y 1),
    x 7 * y 7 + (x 4 * y 1 + x 5 * y 2 + x 6 * y 3)]

/-- The Zorn product as an `R`-bilinear map. -/
def mul : (Fin 8 → R) →ₗ[R] (Fin 8 → R) →ₗ[R] (Fin 8 → R) :=
  LinearMap.mk₂ R (mulFun R)
    (fun x x' y => by funext i; fin_cases i <;> simp [mulFun] <;> ring)
    (fun c x y => by funext i; fin_cases i <;> simp [mulFun] <;> ring)
    (fun x y y' => by funext i; fin_cases i <;> simp [mulFun] <;> ring)
    (fun c x y => by funext i; fin_cases i <;> simp [mulFun] <;> ring)

theorem mul_apply (x y : Fin 8 → R) : mul R x y = mulFun R x y := rfl

/-- The identity `(1, 0, 0, 1)` of the Zorn product. -/
def unit : Fin 8 → R := ![1, 0, 0, 0, 0, 0, 0, 1]

/-- The bilinear form `a b' - u·v'`, whose diagonal is the Zorn norm. -/
def normBilin : LinearMap.BilinForm R (Fin 8 → R) :=
  LinearMap.mk₂ R (fun x y => x 0 * y 7 - (x 1 * y 4 + x 2 * y 5 + x 3 * y 6))
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- The Zorn norm `a b - u·v`. -/
def norm : QuadraticForm R (Fin 8 → R) :=
  (normBilin R).toQuadraticMap

theorem norm_apply (x : Fin 8 → R) :
    norm R x = x 0 * x 7 - (x 1 * x 4 + x 2 * x 5 + x 3 * x 6) := rfl

theorem unit_mul (x : Fin 8 → R) : mul R (unit R) x = x := by
  funext i; fin_cases i <;> simp [mul_apply, mulFun, unit]

theorem mul_unit (x : Fin 8 → R) : mul R x (unit R) = x := by
  funext i; fin_cases i <;> simp [mul_apply, mulFun, unit]

theorem norm_unit : norm R (unit R) = 1 := by
  simp [norm_apply, unit]

theorem norm_mul (x y : Fin 8 → R) : norm R (mul R x y) = norm R x * norm R y := by
  simp only [norm_apply, mul_apply, mulFun, Matrix.cons_val]
  ring

/-- The polar form of the Zorn norm. -/
theorem polar_norm (x y : Fin 8 → R) :
    QuadraticMap.polar (norm R) x y =
      x 0 * y 7 + x 7 * y 0 - (x 1 * y 4 + x 4 * y 1 + x 2 * y 5 + x 5 * y 2 +
        x 3 * y 6 + x 6 * y 3) := by
  rw [norm, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [normBilin, LinearMap.mk₂_apply]
  ring

/-- The polar form of the Zorn norm has zero radical, in every characteristic. -/
theorem polar_nondegenerate (x : Fin 8 → R)
    (hx : ∀ y, QuadraticMap.polar (norm R) x y = 0) : x = 0 := by
  have h : ∀ j : Fin 8, QuadraticMap.polar (norm R) x (Pi.single j 1) = 0 := fun j => hx _
  funext i
  fin_cases i
  · simpa [polar_norm] using h 7
  · simpa [polar_norm] using h 4
  · simpa [polar_norm] using h 5
  · simpa [polar_norm] using h 6
  · simpa [polar_norm] using h 1
  · simpa [polar_norm] using h 2
  · simpa [polar_norm] using h 3
  · simpa [polar_norm] using h 0

/-- The Zorn product commutes with every change of coefficients. -/
theorem map_mulFun {A : Type u} [CommRing A] (φ : R →+* A) (x y : Fin 8 → R) :
    (fun i => φ (mulFun R x y i)) = mulFun A (fun i => φ (x i)) (fun i => φ (y i)) := by
  funext i; fin_cases i <;> simp [mulFun]

end Ring

/-- Every bilinear map on `A⁸` is the double sum of its values on standard basis vectors. -/
theorem bilinear_apply_eq_sum {A : Type u} [CommRing A]
    (B : (Fin 8 → A) →ₗ[A] (Fin 8 → A) →ₗ[A] (Fin 8 → A)) (x y : Fin 8 → A) (i : Fin 8) :
    B x y i = ∑ j, ∑ k, B (Pi.single j 1) (Pi.single k 1) i * x j * y k := by
  have hx : x = ∑ j, x j • Pi.single j (1 : A) := by
    ext a
    simp [Pi.single_apply]
  have hy : y = ∑ k, y k • Pi.single k (1 : A) := by
    ext a
    simp [Pi.single_apply]
  conv_lhs => rw [hx, hy]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end SplitCayley

namespace CayleyDatum

open SplitCayley

/-- The split Cayley datum over a field: Zorn vector matrices with their determinant norm. -/
def split (K : Type u) [Field K] : CayleyDatum K where
  multiplication := SplitCayley.mul K
  unit := SplitCayley.unit K
  norm := SplitCayley.norm K
  unit_mul := SplitCayley.unit_mul K
  mul_unit := SplitCayley.mul_unit K
  norm_unit := SplitCayley.norm_unit K
  norm_mul := SplitCayley.norm_mul K
  polar_nondegenerate := fun x hx => SplitCayley.polar_nondegenerate K x hx

variable {K : Type u} [Field K]

/-- The structure constants of the split datum are those of the Zorn product. -/
theorem split_structureConstant (i j k : Fin 8) :
    (split K).structureConstant i j k = mulFun K (Pi.single j 1) (Pi.single k 1) i := rfl

/-- After any change of coefficients the split multiplication is the Zorn product over the new
coefficient ring. -/
theorem split_multiplicationOver {A : Type u} [CommRing A] (φ : K →+* A)
    (x y : CayleyVector A) :
    (split K).multiplicationOver φ x y = SplitCayley.mul A x y := by
  funext i
  rw [bilinear_apply_eq_sum (SplitCayley.mul A) x y i, multiplicationOver]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [split_structureConstant]
  have h := congrFun (map_mulFun K φ (Pi.single j 1) (Pi.single k 1)) i
  have hj : (fun l => φ ((Pi.single j (1 : K) : Fin 8 → K) l)) = Pi.single j 1 := by
    funext l; by_cases hl : l = j
    · subst hl; simp
    · simp [hl]
  have hk : (fun l => φ ((Pi.single k (1 : K) : Fin 8 → K) l)) = Pi.single k 1 := by
    funext l; by_cases hl : l = k
    · subst hl; simp
    · simp [hl]
  rw [h, hj, hk]
  rfl

/-- After any change of coefficients the split unit is `(1, 0, 0, 1)`. -/
theorem split_unitOver {A : Type u} [CommRing A] (φ : K →+* A) :
    (split K).unitOver φ = SplitCayley.unit A := by
  funext i
  fin_cases i <;> simp [unitOver, split, SplitCayley.unit]

end CayleyDatum

end Langlands.GroupScheme
