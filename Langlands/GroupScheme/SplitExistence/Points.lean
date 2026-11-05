import Langlands.GroupScheme.SplitExistence.RootExp

/-! # Points of the Chevalley group over a field: root groups, torus, Weyl elements

For integral Chevalley data `D` and a field `K`, the root homomorphisms `x j : K → GL_n(K)`, the
torus homomorphism `Hom(X, Kˣ) → GL_n(K)` acting on the basis vector `c` by the character
`wt c`, and the Weyl elements `n_i = φ_i(w)`. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

theorem isDividedPowerFamily (j : J) : IsDividedPowerFamily (D.e j) :=
  ⟨D.e_zero j, D.e_mul j, D.e_eq_zero j⟩

variable {K : Type u} [CommRing K]

/-- The root homomorphism `s ↦ x_j(s)` of the root `j`. -/
def rootHom (j : J) : Multiplicative K →* GL (Fin D.n) K :=
  divExpHom (D.isDividedPowerFamily j)

/-- The root element `x_j(s)`. -/
def x (j : J) (s : K) : GL (Fin D.n) K :=
  D.rootHom j (Multiplicative.ofAdd s)

theorem coe_x (j : J) (s : K) : (D.x j s : Matrix (Fin D.n) (Fin D.n) K) = divExp (D.e j) s :=
  rfl

theorem x_add (j : J) (s t : K) : D.x j (s + t) = D.x j s * D.x j t := by
  rw [x, x, x, ← map_mul]
  rfl

theorem x_zero (j : J) : D.x j (0 : K) = 1 := by
  rw [x, ofAdd_zero, map_one]

theorem x_neg (j : J) (s : K) : D.x j (-s) = (D.x j s)⁻¹ := by
  rw [x, x, ofAdd_neg, map_inv]

/-- The diagonal unit with entries `f c`. -/
def diagUnit (f : Fin D.n → Kˣ) : GL (Fin D.n) K where
  val := diagonal fun c => (f c : K)
  inv := diagonal fun c => (((f c)⁻¹ : Kˣ) : K)
  val_inv := by rw [diagonal_mul_diagonal]; simp
  inv_val := by rw [diagonal_mul_diagonal]; simp

theorem coe_diagUnit (f : Fin D.n → Kˣ) :
    (D.diagUnit f : Matrix (Fin D.n) (Fin D.n) K) = diagonal fun c => (f c : K) :=
  rfl

theorem coe_diagUnit_inv (f : Fin D.n → Kˣ) :
    (((D.diagUnit f)⁻¹ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) =
      diagonal fun c => (((f c)⁻¹ : Kˣ) : K) :=
  rfl

/-- The diagonal unit acting on the basis vector `c` by `χ (wt c)`. -/
def torusHom : (Multiplicative X →* Kˣ) →* GL (Fin D.n) K where
  toFun χ := D.diagUnit fun c => χ (Multiplicative.ofAdd (D.wt c))
  map_one' := by
    ext i j
    simp [coe_diagUnit, diagonal_apply, one_apply]
  map_mul' χ ψ := by
    ext i j
    simp only [Units.val_mul, coe_diagUnit, diagonal_mul_diagonal, MonoidHom.mul_apply]

theorem coe_torusHom (χ : Multiplicative X →* Kˣ) :
    (D.torusHom χ : Matrix (Fin D.n) (Fin D.n) K) =
      diagonal fun c => ((χ (Multiplicative.ofAdd (D.wt c)) : Kˣ) : K) :=
  rfl

/-- Conjugation by a torus point scales the root parameter by the root character. -/
theorem torusHom_conj_x (χ : Multiplicative X →* Kˣ) (j : J) (s : K) :
    D.torusHom χ * D.x j s * (D.torusHom χ)⁻¹ =
      D.x j (((χ (Multiplicative.ofAdd (P.root j)) : Kˣ) : K) * s) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_x, coe_x]
  change (diagonal fun c => ((χ (Multiplicative.ofAdd (D.wt c)) : Kˣ) : K)) * divExp (D.e j) s *
    (diagonal fun c => (((χ (Multiplicative.ofAdd (D.wt c)))⁻¹ : Kˣ) : K)) = _
  ext c d
  rw [mul_diagonal, diagonal_mul]
  simp only [divExp, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Finset.mul_sum,
    Finset.sum_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : D.e j k c d = 0
  · simp [h]
  · have hw := D.e_weight j k c d h
    rw [hw, ofAdd_add, map_mul, ofAdd_nsmul, map_pow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, eq_intCast]
    have hu : ((χ (Multiplicative.ofAdd (D.wt d)) : Kˣ) : K) *
        (((χ (Multiplicative.ofAdd (D.wt d)))⁻¹ : Kˣ) : K) = 1 := Units.mul_inv _
    linear_combination (s ^ k * ((χ (Multiplicative.ofAdd (P.root j)) : Kˣ) : K) ^ k *
      (D.e j k c d : K)) * hu

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
