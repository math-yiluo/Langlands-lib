import Langlands.Representation.Whittaker.CharacterChange
import Langlands.Representation.Whittaker.DualTransform
import Langlands.Representation.Whittaker.Iwasawa

/-! # Shahidi's alternating diagonal and Whittaker sign conventions -/

noncomputable section

namespace Langlands.Shahidi

open GeneralLinear Whittaker HarmonicAnalysis

universe uF uV

variable {F : Type uF} [Field F]

/-- Shahidi's diagonal `diag(-1, 1, -1, ...)`, with one-based source indices. -/
def alternatingDiagonal (n : ℕ) : GeneralLinear n F :=
  Iwasawa.diagonalUnits fun i => (-1 : Fˣ) ^ (i.val + 1)

@[simp] theorem alternatingDiagonal_val (n : ℕ) :
    (alternatingDiagonal (F := F) n).val =
      Matrix.diagonal (fun i : Fin n => (-1 : F) ^ (i.val + 1)) := by
  simp [alternatingDiagonal]

@[simp] theorem alternatingDiagonal_mul_self (n : ℕ) :
    alternatingDiagonal (F := F) n * alternatingDiagonal n = 1 := by
  apply Units.ext
  simp only [Units.val_mul, alternatingDiagonal_val, Units.val_one,
    Matrix.diagonal_mul_diagonal]
  simp_rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  exact Matrix.diagonal_one

/-- Relative to the Library's `diag((-1)^n, ..., 1)`, the source diagonal
has the central factor `(-1)^(n+1)`. -/
theorem alternatingDiagonal_eq_scalar_characterChange (n : ℕ) :
    alternatingDiagonal (F := F) (n + 1) =
      scalar ((-1 : Fˣ) ^ (n + 1)) * characterChangeElement (-1) n := by
  apply Units.ext
  simp only [alternatingDiagonal_val, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    characterChangeElement_val,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  change Matrix.diagonal (fun i : Fin (n + 1) => (-1 : F) ^ (i.val + 1)) =
    Matrix.diagonal (fun _ => (-1 : F) ^ (n + 1)) *
      Matrix.diagonal (fun i : Fin (n + 1) => (-1 : F) ^ (n - i.val))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have he : n + 1 + (n - i.val) = i.val + 1 + 2 * (n - i.val) := by omega
  rw [← pow_add, he]
  simp [pow_add, pow_mul]

/-- The central factor cancels in conjugation: the same actual unipotent
conjugation as the Library's change by `-1` moves past the source diagonal. -/
theorem alternatingDiagonal_mul_unipotent (n : ℕ)
    (u : upperUnipotent (n + 1) F) :
    alternatingDiagonal (n + 1) * u.val =
      (characterChangeConj (-1) n u).val * alternatingDiagonal (n + 1) := by
  rw [alternatingDiagonal_eq_scalar_characterChange, mul_assoc,
    characterChangeElement_mul, ← mul_assoc,
    Matrix.GeneralLinearGroup.scalar_commute, mul_assoc]

/-- Left translation by the actual alternating diagonal, on all functions. -/
def alternatingTranslate (n : ℕ) :
    (GeneralLinear (n + 1) F → ℂ) ≃ₗ[ℂ] (GeneralLinear (n + 1) F → ℂ) where
  toFun f g := f (alternatingDiagonal (n + 1) * g)
  invFun f g := f (alternatingDiagonal (n + 1) * g)
  left_inv f := by
    funext g
    simp only [← mul_assoc, alternatingDiagonal_mul_self, one_mul]
  right_inv f := by
    funext g
    simp only [← mul_assoc, alternatingDiagonal_mul_self, one_mul]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem alternatingTranslate_apply (n : ℕ) (f : GeneralLinear (n + 1) F → ℂ)
    (g : GeneralLinear (n + 1) F) :
    alternatingTranslate n f g = f (alternatingDiagonal (n + 1) * g) := rfl

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- The source's `W(ε_n g)` has exactly the inverse unipotent character. -/
theorem alternatingTranslate_mem (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    {f : GeneralLinear (n + 1) F → ℂ}
    (hf : f ∈ (equivariantFunctions (upperUnipotent (n + 1) F)
      (standardCharacter ψ n)).toSubmodule) :
    alternatingTranslate n f ∈ (equivariantFunctions (upperUnipotent (n + 1) F)
      (inverseStandardCharacter ψ n)).toSubmodule := by
  intro u g
  change f (alternatingDiagonal (n + 1) * (u.val * g)) = _
  rw [← mul_assoc, alternatingDiagonal_mul_unipotent, mul_assoc, hf,
    standardCharacter_characterChangeConj]
  have he : standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n :=
    scaledStandardCharacter_neg_one ψ n
  rw [he]
  rfl

/-- Shahidi's modified dual transform, including the alternating diagonal. -/
def sourceDualFunction (n : ℕ) :
    (GeneralLinear (n + 1) F → ℂ) →ₗ[ℂ] (GeneralLinear (n + 1) F → ℂ) :=
  (dualFunction n).toLinearMap.comp (alternatingTranslate n).toLinearMap

@[simp] theorem sourceDualFunction_apply (n : ℕ) (f : GeneralLinear (n + 1) F → ℂ)
    (g : GeneralLinear (n + 1) F) :
    sourceDualFunction n f g =
      f (alternatingDiagonal (n + 1) * weylLong (n + 1) F *
        inverseTranspose (n + 1) F g) := by
  simp only [sourceDualFunction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    dualFunction_apply, alternatingTranslate_apply, mul_assoc]

/-- The two character reversals cancel, so the source dual transform keeps ψ. -/
theorem sourceDualFunction_mem (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    {f : GeneralLinear (n + 1) F → ℂ}
    (hf : f ∈ (equivariantFunctions (upperUnipotent (n + 1) F)
      (standardCharacter ψ n)).toSubmodule) :
    sourceDualFunction n f ∈ (equivariantFunctions (upperUnipotent (n + 1) F)
      (standardCharacter ψ n)).toSubmodule :=
  dualFunction_inverse_mem ψ (alternatingTranslate_mem ψ n hf)

section Coefficients

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  (π : Representation ℂ (GeneralLinear (n + 1) F) V)

/-- Translate an actual ψ-functional to an actual ψ-inverse functional. -/
def alternatingFunctional (ψ : UnitaryAdditiveCharacter F) (ℓ : glFunctionals ψ n π) :
    glInverseFunctionals ψ n π :=
  ⟨ℓ.val.comp (π (alternatingDiagonal (n + 1))), by
    intro u v
    change ℓ.val (π (alternatingDiagonal (n + 1)) (π u.val v)) = _
    rw [← Module.End.mul_apply, ← map_mul, alternatingDiagonal_mul_unipotent,
      map_mul, Module.End.mul_apply, ℓ.property, standardCharacter_characterChangeConj]
    have he : standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n :=
      scaledStandardCharacter_neg_one ψ n
    rw [he]
    rfl⟩

/-- The translated coefficient is precisely the source's second integrand factor. -/
theorem alternatingFunctional_coefficient (ψ : UnitaryAdditiveCharacter F)
    (ℓ : glFunctionals ψ n π) (v : V) (g : GeneralLinear (n + 1) F) :
    (coefficientMap π (alternatingFunctional π ψ ℓ) v).val g =
      (coefficientMap π ℓ v).val (alternatingDiagonal (n + 1) * g) := by
  change ℓ.val (π (alternatingDiagonal (n + 1)) (π g v)) = _
  rw [← Module.End.mul_apply, ← map_mul]
  rfl

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- For a prescribed actual scalar action, the source translation and the
Library's character change differ by `ω(-1)^(n+1)`. -/
theorem matrixCoefficient_alternatingDiagonal
    (ω : Fˣ →* ℂˣ)
    (hω : ∀ (z : Fˣ) (v : V), π (scalar z) v = (ω z : ℂ) • v)
    (ℓ : Module.Dual ℂ V) (v : V) (g : GeneralLinear (n + 1) F) :
    matrixCoefficient π ℓ v (alternatingDiagonal (n + 1) * g) =
      (ω (-1) : ℂ) ^ (n + 1) *
        matrixCoefficient π ℓ v (characterChangeElement (-1) n * g) := by
  rw [alternatingDiagonal_eq_scalar_characterChange, mul_assoc]
  change ℓ (π (scalar ((-1 : Fˣ) ^ (n + 1)) *
    (characterChangeElement (-1) n * g)) v) = _
  rw [map_mul, Module.End.mul_apply, hω, map_smul]
  simp only [map_pow, Units.val_pow_eq_pow_val, smul_eq_mul]
  rfl

end Coefficients

end Langlands.Shahidi
