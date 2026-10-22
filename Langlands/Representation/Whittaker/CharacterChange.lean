import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.HarmonicAnalysis.CharacterTransport
import Mathlib.Tactic.LinearCombination

/-!
# Change of the additive character on Whittaker functionals

For `a : Fˣ`, the diagonal matrix `d_a = diag(a^n, ..., a, 1)` in `GL_(n+1)(F)`
conjugates the standard character of `ψ` into that of `x ↦ ψ(a*x)`. Translating
functionals by `π(d_a)` identifies the two functional spaces, and coefficient
functions are left-translated by `d_a`.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

section Element

variable {F : Type uF} [Field F]

/-- The diagonal matrix `diag(a^n, a^(n-1), ..., a, 1)` in `GL_(n+1)(F)`. -/
def characterChangeElement (a : Fˣ) (n : ℕ) : Langlands.GeneralLinear (n + 1) F where
  val := Matrix.diagonal fun i => ((a ^ (n - i.val) : Fˣ) : F)
  inv := Matrix.diagonal fun i => (((a ^ (n - i.val))⁻¹ : Fˣ) : F)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

@[simp] theorem characterChangeElement_val (a : Fˣ) (n : ℕ) :
    (characterChangeElement a n).val =
      Matrix.diagonal fun i => ((a ^ (n - i.val) : Fˣ) : F) := rfl

@[simp] theorem characterChangeElement_inv_val (a : Fˣ) (n : ℕ) :
    (characterChangeElement a n)⁻¹.val =
      Matrix.diagonal fun i => (((a ^ (n - i.val))⁻¹ : Fˣ) : F) := rfl

/-- The inverse of `d_a` is `d_(a⁻¹)`. -/
theorem characterChangeElement_inv (a : Fˣ) (n : ℕ) :
    (characterChangeElement a n)⁻¹ = characterChangeElement a⁻¹ n := by
  apply Units.ext
  simp only [characterChangeElement_inv_val, characterChangeElement_val, inv_pow]

@[simp] theorem characterChangeElement_one (n : ℕ) :
    characterChangeElement (1 : Fˣ) n = 1 := by
  apply Units.ext
  simp [Matrix.diagonal_one]

/-- The entries of a conjugate by `d_a`. -/
theorem characterChangeElement_conj_apply (a : Fˣ) (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) (i j : Fin (n + 1)) :
    (characterChangeElement a n * g * (characterChangeElement a n)⁻¹).val i j =
      ((a ^ (n - i.val) : Fˣ) : F) * g.val i j * (((a ^ (n - j.val))⁻¹ : Fˣ) : F) := by
  simp only [Units.val_mul, characterChangeElement_val, characterChangeElement_inv_val,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Conjugation by `d_a` preserves the upper-unipotent subgroup. -/
def characterChangeConj (a : Fˣ) (n : ℕ) :
    upperUnipotent (n + 1) F →* upperUnipotent (n + 1) F :=
  ((MulAut.conj (characterChangeElement a n)).toMonoidHom.comp
    (upperUnipotent (n + 1) F).subtype).codRestrict (upperUnipotent (n + 1) F) (by
      intro u
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · change (characterChangeElement a n * u.val * (characterChangeElement a n)⁻¹).val i j = 0
        have h0 : u.val.val i j = 0 := UpperUnipotent.entry_eq_zero u (show j < i from hij)
        rw [characterChangeElement_conj_apply, h0, mul_zero, zero_mul]
      · change (characterChangeElement a n * u.val * (characterChangeElement a n)⁻¹).val i i = 1
        rw [characterChangeElement_conj_apply, UpperUnipotent.entry_diag, mul_one,
          Units.mul_inv])

@[simp] theorem characterChangeConj_val (a : Fˣ) (n : ℕ) (u : upperUnipotent (n + 1) F) :
    ((characterChangeConj a n u : upperUnipotent (n + 1) F) : Langlands.GeneralLinear (n + 1) F) =
      characterChangeElement a n * u.val * (characterChangeElement a n)⁻¹ := rfl

/-- Moving `d_a` past a unipotent matrix conjugates it. -/
theorem characterChangeElement_mul (a : Fˣ) (n : ℕ) (u : upperUnipotent (n + 1) F) :
    characterChangeElement a n * u.val =
      (characterChangeConj a n u).val * characterChangeElement a n := by
  rw [characterChangeConj_val, inv_mul_cancel_right]

/-- Conjugation by `d_a` multiplies each first-superdiagonal entry by `a`. -/
theorem characterChangeConj_adjacent (a : Fˣ) (n : ℕ) (u : upperUnipotent (n + 1) F)
    (i : Fin n) :
    (characterChangeConj a n u).val.val i.castSucc i.succ =
      (a : F) * u.val.val i.castSucc i.succ := by
  change (characterChangeElement a n * u.val * (characterChangeElement a n)⁻¹).val
    i.castSucc i.succ = _
  have h : n - (i.castSucc : Fin (n + 1)).val = (n - (i.succ : Fin (n + 1)).val) + 1 := by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  rw [characterChangeElement_conj_apply, h, pow_succ, Units.val_mul]
  have hxy : ((a ^ (n - (i.succ : Fin (n + 1)).val) : Fˣ) : F) *
      (((a ^ (n - (i.succ : Fin (n + 1)).val))⁻¹ : Fˣ) : F) = 1 := Units.mul_inv _
  linear_combination ((a : F) * u.val.val i.castSucc i.succ) * hxy

end Element

section Characters

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ : UnitaryAdditiveCharacter F)

/-- The standard character of `ψ` on the conjugate by `d_a` is the standard
character of `ψ.scale a`. -/
theorem standardCharacter_characterChangeConj (a : Fˣ) (n : ℕ)
    (u : upperUnipotent (n + 1) F) :
    standardCharacter ψ n (characterChangeConj a n u) = standardCharacter (ψ.scale a) n u := by
  apply Units.ext
  simp only [standardCharacter_apply, characterChangeConj_adjacent, ← Finset.mul_sum]
  rfl

/-- The inverse-character version of `standardCharacter_characterChangeConj`. -/
theorem inverseStandardCharacter_characterChangeConj (a : Fˣ) (n : ℕ)
    (u : upperUnipotent (n + 1) F) :
    inverseStandardCharacter ψ n (characterChangeConj a n u) =
      inverseStandardCharacter (ψ.scale a) n u := by
  change (standardCharacter ψ n (characterChangeConj a n u))⁻¹ =
    (standardCharacter (ψ.scale a) n u)⁻¹
  rw [standardCharacter_characterChangeConj]

/-- Scaling back by `a⁻¹` recovers the character of `ψ`. -/
theorem standardCharacter_scale_characterChangeConj_inv (a : Fˣ) (n : ℕ)
    (u : upperUnipotent (n + 1) F) :
    standardCharacter (ψ.scale a) n (characterChangeConj a⁻¹ n u) = standardCharacter ψ n u := by
  rw [standardCharacter_characterChangeConj, UnitaryAdditiveCharacter.scale_scale,
    mul_inv_cancel, UnitaryAdditiveCharacter.scale_one]

theorem inverseStandardCharacter_scale_characterChangeConj_inv (a : Fˣ) (n : ℕ)
    (u : upperUnipotent (n + 1) F) :
    inverseStandardCharacter (ψ.scale a) n (characterChangeConj a⁻¹ n u) =
      inverseStandardCharacter ψ n u := by
  change (standardCharacter (ψ.scale a) n (characterChangeConj a⁻¹ n u))⁻¹ =
    (standardCharacter ψ n u)⁻¹
  rw [standardCharacter_scale_characterChangeConj_inv]

end Characters

section Functionals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The functional `v ↦ ℓ(π(d_a) v)` for the character `ψ.scale a`
(JPSS 1983, page 385). -/
def characterChangeFunctional (a : Fˣ) (ℓ : glFunctionals ψ n π) :
    glFunctionals (ψ.scale a) n π :=
  ⟨ℓ.val.comp (π (characterChangeElement a n)), by
    intro u v
    change ℓ.val (π (characterChangeElement a n) (π u.val v)) =
      (standardCharacter (ψ.scale a) n u : ℂ) * ℓ.val (π (characterChangeElement a n) v)
    rw [← Module.End.mul_apply, ← map_mul, characterChangeElement_mul, map_mul,
      Module.End.mul_apply, ℓ.property, standardCharacter_characterChangeConj]⟩

@[simp] theorem characterChangeFunctional_apply (a : Fˣ) (ℓ : glFunctionals ψ n π) (v : V) :
    (characterChangeFunctional ψ π a ℓ).val v = ℓ.val (π (characterChangeElement a n) v) := rfl

/-- The same translation for inverse-character functionals. -/
def characterChangeInverseFunctional (a : Fˣ) (ℓ : glInverseFunctionals ψ n π) :
    glInverseFunctionals (ψ.scale a) n π :=
  ⟨ℓ.val.comp (π (characterChangeElement a n)), by
    intro u v
    change ℓ.val (π (characterChangeElement a n) (π u.val v)) =
      (inverseStandardCharacter (ψ.scale a) n u : ℂ) *
        ℓ.val (π (characterChangeElement a n) v)
    rw [← Module.End.mul_apply, ← map_mul, characterChangeElement_mul, map_mul,
      Module.End.mul_apply, ℓ.property, inverseStandardCharacter_characterChangeConj]⟩

@[simp] theorem characterChangeInverseFunctional_apply (a : Fˣ)
    (ℓ : glInverseFunctionals ψ n π) (v : V) :
    (characterChangeInverseFunctional ψ π a ℓ).val v =
      ℓ.val (π (characterChangeElement a n) v) := rfl

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- Translating by `d_a` and then by `d_(a⁻¹)` is the identity. -/
theorem translate_characterChangeElement_inv (a : Fˣ) (v : V) :
    π (characterChangeElement a n) (π (characterChangeElement a⁻¹ n) v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, ← characterChangeElement_inv, mul_inv_cancel,
    map_one, Module.End.one_apply]

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem translate_characterChangeElement_inv' (a : Fˣ) (v : V) :
    π (characterChangeElement a⁻¹ n) (π (characterChangeElement a n) v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, ← characterChangeElement_inv, inv_mul_cancel,
    map_one, Module.End.one_apply]

/-- Translation by `π(d_a)` is a linear equivalence between the standard
functionals for `ψ` and for `ψ.scale a`. -/
def characterChangeFunctionalEquiv (a : Fˣ) :
    glFunctionals ψ n π ≃ₗ[ℂ] glFunctionals (ψ.scale a) n π where
  toFun := characterChangeFunctional ψ π a
  invFun ℓ := ⟨ℓ.val.comp (π (characterChangeElement a⁻¹ n)), by
    intro u v
    change ℓ.val (π (characterChangeElement a⁻¹ n) (π u.val v)) =
      (standardCharacter ψ n u : ℂ) * ℓ.val (π (characterChangeElement a⁻¹ n) v)
    rw [← Module.End.mul_apply, ← map_mul, characterChangeElement_mul, map_mul,
      Module.End.mul_apply, ℓ.property, standardCharacter_scale_characterChangeConj_inv]⟩
  left_inv ℓ := by
    apply Subtype.ext
    ext v
    change ℓ.val (π (characterChangeElement a n) (π (characterChangeElement a⁻¹ n) v)) =
      ℓ.val v
    rw [translate_characterChangeElement_inv]
  right_inv ℓ := by
    apply Subtype.ext
    ext v
    change ℓ.val (π (characterChangeElement a⁻¹ n) (π (characterChangeElement a n) v)) =
      ℓ.val v
    rw [translate_characterChangeElement_inv']
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inverse-character version of `characterChangeFunctionalEquiv`. -/
def characterChangeInverseFunctionalEquiv (a : Fˣ) :
    glInverseFunctionals ψ n π ≃ₗ[ℂ] glInverseFunctionals (ψ.scale a) n π where
  toFun := characterChangeInverseFunctional ψ π a
  invFun ℓ := ⟨ℓ.val.comp (π (characterChangeElement a⁻¹ n)), by
    intro u v
    change ℓ.val (π (characterChangeElement a⁻¹ n) (π u.val v)) =
      (inverseStandardCharacter ψ n u : ℂ) * ℓ.val (π (characterChangeElement a⁻¹ n) v)
    rw [← Module.End.mul_apply, ← map_mul, characterChangeElement_mul, map_mul,
      Module.End.mul_apply, ℓ.property, inverseStandardCharacter_scale_characterChangeConj_inv]⟩
  left_inv ℓ := by
    apply Subtype.ext
    ext v
    change ℓ.val (π (characterChangeElement a n) (π (characterChangeElement a⁻¹ n) v)) =
      ℓ.val v
    rw [translate_characterChangeElement_inv]
  right_inv ℓ := by
    apply Subtype.ext
    ext v
    change ℓ.val (π (characterChangeElement a⁻¹ n) (π (characterChangeElement a n) v)) =
      ℓ.val v
    rw [translate_characterChangeElement_inv']
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coefficients of the translated functional are the left translates by `d_a`. -/
theorem characterChangeFunctional_coefficient (a : Fˣ) (ℓ : glFunctionals ψ n π) (v : V)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (coefficientMap π (characterChangeFunctional ψ π a ℓ) v).val g =
      (coefficientMap π ℓ v).val (characterChangeElement a n * g) := by
  change ℓ.val (π (characterChangeElement a n) (π g v)) =
    ℓ.val (π (characterChangeElement a n * g) v)
  rw [map_mul, Module.End.mul_apply]

theorem characterChangeInverseFunctional_coefficient (a : Fˣ)
    (ℓ : glInverseFunctionals ψ n π) (v : V) (g : Langlands.GeneralLinear (n + 1) F) :
    (coefficientMap π (characterChangeInverseFunctional ψ π a ℓ) v).val g =
      (coefficientMap π ℓ v).val (characterChangeElement a n * g) := by
  change ℓ.val (π (characterChangeElement a n) (π g v)) =
    ℓ.val (π (characterChangeElement a n * g) v)
  rw [map_mul, Module.End.mul_apply]

end Functionals

section Functions

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ : UnitaryAdditiveCharacter F) (n : ℕ)

/-- Left translation by `d_a` maps standard Whittaker functions for `ψ` to
those for `ψ.scale a`. -/
def characterChangeFunction (a : Fˣ) :
    (equivariantFunctions (upperUnipotent (n + 1) F) (standardCharacter ψ n)).toSubmodule →ₗ[ℂ]
      (equivariantFunctions (upperUnipotent (n + 1) F)
        (standardCharacter (ψ.scale a) n)).toSubmodule where
  toFun f := ⟨fun g => f.val (characterChangeElement a n * g), by
    intro u g
    change f.val (characterChangeElement a n * (u.val * g)) =
      (standardCharacter (ψ.scale a) n u : ℂ) * f.val (characterChangeElement a n * g)
    rw [← mul_assoc, characterChangeElement_mul, mul_assoc, f.property,
      standardCharacter_characterChangeConj]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem characterChangeFunction_apply (a : Fˣ)
    (f : (equivariantFunctions (upperUnipotent (n + 1) F) (standardCharacter ψ n)).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (characterChangeFunction ψ n a f).val g = f.val (characterChangeElement a n * g) := rfl

/-- Left translation by `d_a` on inverse-character Whittaker functions. -/
def characterChangeInverseFunction (a : Fˣ) :
    (equivariantFunctions (upperUnipotent (n + 1) F)
        (inverseStandardCharacter ψ n)).toSubmodule →ₗ[ℂ]
      (equivariantFunctions (upperUnipotent (n + 1) F)
        (inverseStandardCharacter (ψ.scale a) n)).toSubmodule where
  toFun f := ⟨fun g => f.val (characterChangeElement a n * g), by
    intro u g
    change f.val (characterChangeElement a n * (u.val * g)) =
      (inverseStandardCharacter (ψ.scale a) n u : ℂ) * f.val (characterChangeElement a n * g)
    rw [← mul_assoc, characterChangeElement_mul, mul_assoc, f.property,
      inverseStandardCharacter_characterChangeConj]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem characterChangeInverseFunction_apply (a : Fˣ)
    (f : (equivariantFunctions (upperUnipotent (n + 1) F)
      (inverseStandardCharacter ψ n)).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (characterChangeInverseFunction ψ n a f).val g = f.val (characterChangeElement a n * g) := rfl

variable {n} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The coefficient model of the translated functional is the image of the
coefficient model of `ℓ` under left translation by `d_a`. -/
theorem characterChangeFunction_coefficientModel (a : Fˣ) (ℓ : glFunctionals ψ n π) :
    (coefficientModel π (characterChangeFunctional ψ π a ℓ)).toSubmodule =
      (coefficientModel π ℓ).toSubmodule.map (characterChangeFunction ψ n a) := by
  ext W
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨coefficientMap π ℓ v, ⟨v, rfl⟩, ?_⟩
    apply Subtype.ext
    funext g
    exact (characterChangeFunctional_coefficient ψ π a ℓ v g).symm
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨v, ?_⟩
    apply Subtype.ext
    funext g
    exact characterChangeFunctional_coefficient ψ π a ℓ v g

theorem characterChangeInverseFunction_coefficientModel (a : Fˣ)
    (ℓ : glInverseFunctionals ψ n π) :
    (coefficientModel π (characterChangeInverseFunctional ψ π a ℓ)).toSubmodule =
      (coefficientModel π ℓ).toSubmodule.map (characterChangeInverseFunction ψ n a) := by
  ext W
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨coefficientMap π ℓ v, ⟨v, rfl⟩, ?_⟩
    apply Subtype.ext
    funext g
    exact (characterChangeInverseFunctional_coefficient ψ π a ℓ v g).symm
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨v, ?_⟩
    apply Subtype.ext
    funext g
    exact characterChangeInverseFunctional_coefficient ψ π a ℓ v g

end Functions

end Langlands.Whittaker
