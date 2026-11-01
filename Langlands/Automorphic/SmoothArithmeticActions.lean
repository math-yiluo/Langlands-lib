import Langlands.Automorphic.SmoothArithmeticTransport

/-! # Rational automorphism and CM actions on actual smooth adelic functions -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ContinuousRationalFunctions

open Langlands.Global AdelicGLTransport

variable {K : Type uK} [Field K] [NumberField K]

/-- The actual rational automorphism action uses inverse arithmetic pullback. -/
def smoothGaloisAut (n : ℕ) : (K ≃ₐ[ℚ] K) →*
    (SmoothRationalFunctions K n ≃L[ℂ] SmoothRationalFunctions K n) where
  toFun σ := smoothEquiv n σ.toRingEquiv.symm
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact smoothEquiv_refl n f
  map_mul' σ τ := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact smoothEquiv_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f

@[simp] theorem smoothGaloisAut_val (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : SmoothRationalFunctions K n) :
    (smoothGaloisAut n σ f).val = galoisAut n σ f.val := rfl

@[simp] theorem evaluate_smoothGaloisAut (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : SmoothRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (smoothGaloisAut n σ f).val x =
      evaluate K n f.val (AdelicGLTransport.adelicAut n (σ⁻¹) x) := rfl

/-- Installable additive left action on the actual smooth subspace. -/
@[instance_reducible]
def smoothGaloisAction (n : ℕ) :
    DistribMulAction (K ≃ₐ[ℚ] K) (SmoothRationalFunctions K n) where
  smul σ f := smoothGaloisAut n σ f
  one_smul f := by
    change smoothGaloisAut n 1 f = f
    rw [map_one]
    rfl
  mul_smul σ τ f := by
    change smoothGaloisAut n (σ * τ) f = smoothGaloisAut n σ (smoothGaloisAut n τ f)
    rw [map_mul]
    rfl
  smul_zero σ := map_zero (smoothGaloisAut n σ)
  smul_add σ := map_add (smoothGaloisAut n σ)

theorem smoothGaloisAut_rightAction (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (g : AdelicGL K n) (f : SmoothRationalFunctions K n) :
    smoothGaloisAut n σ
        (smoothRightAction K n (AdelicGLTransport.adelicAut n (σ⁻¹) g) f) =
      smoothRightAction K n g (smoothGaloisAut n σ f) :=
  smoothEquiv_rightAction n σ.toRingEquiv.symm g f

/-- The same action on smooth functions with a common open finite stabilizer. -/
def finiteSmoothGaloisAut (n : ℕ) : (K ≃ₐ[ℚ] K) →*
    (FiniteSmoothRationalFunctions K n ≃L[ℂ] FiniteSmoothRationalFunctions K n) where
  toFun σ := finiteSmoothEquiv n σ.toRingEquiv.symm
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact finiteSmoothEquiv_refl n f
  map_mul' σ τ := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact finiteSmoothEquiv_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f

@[simp] theorem finiteSmoothGaloisAut_val (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : FiniteSmoothRationalFunctions K n) :
    (finiteSmoothGaloisAut n σ f).val = galoisAut n σ f.val := rfl

@[simp] theorem evaluate_finiteSmoothGaloisAut (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : FiniteSmoothRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (finiteSmoothGaloisAut n σ f).val x =
      evaluate K n f.val (AdelicGLTransport.adelicAut n (σ⁻¹) x) := rfl

/-- Installable additive left action on the stronger common-stabilizer space. -/
@[instance_reducible]
def finiteSmoothGaloisAction (n : ℕ) :
    DistribMulAction (K ≃ₐ[ℚ] K) (FiniteSmoothRationalFunctions K n) where
  smul σ f := finiteSmoothGaloisAut n σ f
  one_smul f := by
    change finiteSmoothGaloisAut n 1 f = f
    rw [map_one]
    rfl
  mul_smul σ τ f := by
    change finiteSmoothGaloisAut n (σ * τ) f =
      finiteSmoothGaloisAut n σ (finiteSmoothGaloisAut n τ f)
    rw [map_mul]
    rfl
  smul_zero σ := map_zero (finiteSmoothGaloisAut n σ)
  smul_add σ := map_add (finiteSmoothGaloisAut n σ)

theorem finiteSmoothGaloisAut_rightAction (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (g : AdelicGL K n) (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothGaloisAut n σ
        (finiteSmoothRightAction K n (AdelicGLTransport.adelicAut n (σ⁻¹) g) f) =
      finiteSmoothRightAction K n g (finiteSmoothGaloisAut n σ f) :=
  finiteSmoothEquiv_rightAction n σ.toRingEquiv.symm g f

/-- The actual inclusion of the stronger space commutes with the rational action. -/
theorem smoothGaloisAut_finiteSmoothInclusion (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : FiniteSmoothRationalFunctions K n) :
    smoothGaloisAut n σ (finiteSmoothInclusion K n f) =
      finiteSmoothInclusion K n (finiteSmoothGaloisAut n σ f) :=
  smoothEquiv_finiteSmoothInclusion n σ.toRingEquiv.symm f

/-- The smooth specified-character spaces follow the actual Hecke Galois action. -/
def smoothGaloisCentralCharacterEquiv (n : ℕ) (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K) :
    (smoothCentralCharacterSubrepresentation K n χ).toSubmodule ≃L[ℂ]
      (smoothCentralCharacterSubrepresentation K n
        (HeckeCharacter.galoisAut σ χ)).toSubmodule :=
  smoothCentralCharacterEquiv n σ.toRingEquiv.symm χ

@[simp] theorem evaluate_smoothGaloisCentralCharacterEquiv (n : ℕ)
    (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K)
    (f : (smoothCentralCharacterSubrepresentation K n χ).toSubmodule)
    (x : AdelicGL K n) :
    evaluate K n (smoothGaloisCentralCharacterEquiv n σ χ f).val x =
      evaluate K n f.val (AdelicGLTransport.adelicAut n (σ⁻¹) x) := rfl

@[simp] theorem hasFiniteLevel_smoothGaloisAut_iff (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : SmoothRationalFunctions K n) :
    HasFiniteLevel K n (smoothGaloisAut n σ f).val ↔ HasFiniteLevel K n f.val :=
  hasFiniteLevel_arithmeticComap_iff n σ.toRingEquiv.symm f.val

section CM
variable [NumberField.IsCMField K]

/-- Direct CM conjugation of the argument on the actual smooth function space. -/
def smoothComplexConj (n : ℕ) :
    SmoothRationalFunctions K n ≃L[ℂ] SmoothRationalFunctions K n :=
  smoothEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv

@[simp] theorem smoothComplexConj_val (n : ℕ) (f : SmoothRationalFunctions K n) :
    (smoothComplexConj n f).val = complexConj n f.val := rfl

@[simp] theorem evaluate_smoothComplexConj (n : ℕ) (f : SmoothRationalFunctions K n)
    (x : AdelicGL K n) :
    evaluate K n (smoothComplexConj n f).val x =
      evaluate K n f.val (CMConjugation.adelicConj K n x) :=
  evaluate_complexConj n f.val x

@[simp] theorem smoothComplexConj_smoothComplexConj (n : ℕ)
    (f : SmoothRationalFunctions K n) :
    smoothComplexConj n (smoothComplexConj n f) = f := by
  apply Subtype.ext
  exact complexConj_complexConj n f.val

@[simp] theorem smoothGaloisAut_complexConj (n : ℕ) (f : SmoothRationalFunctions K n) :
    smoothGaloisAut n ((NumberField.IsCMField.complexConj K).restrictScalars ℚ) f =
      smoothComplexConj n f := by
  apply Subtype.ext
  exact galoisAut_complexConj n f.val

theorem smoothComplexConj_rightAction (n : ℕ)
    (g : AdelicGL K n) (f : SmoothRationalFunctions K n) :
    smoothComplexConj n (smoothRightAction K n (CMConjugation.adelicConj K n g) f) =
      smoothRightAction K n g (smoothComplexConj n f) := by
  have h := smoothEquiv_rightAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv g f
  rwa [adelicEquiv_complexConj] at h

/-- Direct argument conjugation on the common finite stabilizer subspace. -/
def finiteSmoothComplexConj (n : ℕ) :
    FiniteSmoothRationalFunctions K n ≃L[ℂ] FiniteSmoothRationalFunctions K n :=
  finiteSmoothEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv

@[simp] theorem finiteSmoothComplexConj_val (n : ℕ)
    (f : FiniteSmoothRationalFunctions K n) :
    (finiteSmoothComplexConj n f).val = complexConj n f.val := rfl

@[simp] theorem evaluate_finiteSmoothComplexConj (n : ℕ)
    (f : FiniteSmoothRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (finiteSmoothComplexConj n f).val x =
      evaluate K n f.val (CMConjugation.adelicConj K n x) :=
  evaluate_complexConj n f.val x

@[simp] theorem finiteSmoothComplexConj_finiteSmoothComplexConj (n : ℕ)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothComplexConj n (finiteSmoothComplexConj n f) = f := by
  apply Subtype.ext
  exact complexConj_complexConj n f.val

@[simp] theorem finiteSmoothGaloisAut_complexConj (n : ℕ)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothGaloisAut n ((NumberField.IsCMField.complexConj K).restrictScalars ℚ) f =
      finiteSmoothComplexConj n f := by
  apply Subtype.ext
  exact galoisAut_complexConj n f.val

theorem finiteSmoothComplexConj_rightAction (n : ℕ)
    (g : AdelicGL K n) (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothComplexConj n
        (finiteSmoothRightAction K n (CMConjugation.adelicConj K n g) f) =
      finiteSmoothRightAction K n g (finiteSmoothComplexConj n f) := by
  have h := finiteSmoothEquiv_rightAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv g f
  rwa [adelicEquiv_complexConj] at h

theorem smoothComplexConj_finiteSmoothInclusion (n : ℕ)
    (f : FiniteSmoothRationalFunctions K n) :
    smoothComplexConj n (finiteSmoothInclusion K n f) =
      finiteSmoothInclusion K n (finiteSmoothComplexConj n f) :=
  smoothEquiv_finiteSmoothInclusion n
    (NumberField.IsCMField.complexConj K).toRingEquiv f

/-- CM conjugation carries the specified character to its existing argument conjugate. -/
def smoothCMCentralCharacterEquiv (n : ℕ) (χ : HeckeCharacter K) :
    (smoothCentralCharacterSubrepresentation K n χ).toSubmodule ≃L[ℂ]
      (smoothCentralCharacterSubrepresentation K n χ.complexConj).toSubmodule :=
  smoothCentralCharacterEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv χ

@[simp] theorem evaluate_smoothCMCentralCharacterEquiv (n : ℕ) (χ : HeckeCharacter K)
    (f : (smoothCentralCharacterSubrepresentation K n χ).toSubmodule)
    (x : AdelicGL K n) :
    evaluate K n (smoothCMCentralCharacterEquiv n χ f).val x =
      evaluate K n f.val (CMConjugation.adelicConj K n x) :=
  evaluate_complexConj n f.val x

@[simp] theorem hasFiniteLevel_smoothComplexConj_iff (n : ℕ)
    (f : SmoothRationalFunctions K n) :
    HasFiniteLevel K n (smoothComplexConj n f).val ↔ HasFiniteLevel K n f.val :=
  hasFiniteLevel_complexConj_iff n f.val

/-- This uses the proved invariance of the actual standard infinite compact. -/
@[simp] theorem isStandardInfiniteFinite_smoothComplexConj_iff (n : ℕ)
    (f : SmoothRationalFunctions K n) :
    IsInfiniteFinite K n (standardInfiniteCompact K n) (smoothComplexConj n f).val ↔
      IsInfiniteFinite K n (standardInfiniteCompact K n) f.val :=
  isStandardInfiniteFinite_complexConj_iff n f.val

end CM
end Langlands.Automorphic.ContinuousRationalFunctions
