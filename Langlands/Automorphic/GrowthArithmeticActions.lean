import Langlands.Automorphic.GrowthArithmeticTransport
import Langlands.Automorphic.SmoothArithmeticActions

/-! # Rational automorphism and CM actions on actual adelic growth spaces -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ContinuousRationalFunctions

open Langlands.Global AdelicGLTransport

variable {K : Type uK} [Field K] [NumberField K]

/-- Inverse arithmetic pullback on this actual growth space. -/
def polynomialGrowthGaloisAut (n : ℕ) : (K ≃ₐ[ℚ] K) →*
    (PolynomialGrowthRationalFunctions K n ≃L[ℂ] PolynomialGrowthRationalFunctions K n) where
  toFun σ := polynomialGrowthEquiv n σ.toRingEquiv.symm
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact polynomialGrowthEquiv_refl n f
  map_mul' σ τ := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact polynomialGrowthEquiv_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f

@[simp] theorem polynomialGrowthGaloisAut_val (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : PolynomialGrowthRationalFunctions K n) :
    (polynomialGrowthGaloisAut n σ f).val = galoisAut n σ f.val := rfl

@[simp] theorem evaluate_polynomialGrowthGaloisAut (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : PolynomialGrowthRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (polynomialGrowthGaloisAut n σ f).val x =
      evaluate K n f.val (AdelicGLTransport.adelicAut n (σ⁻¹) x) := rfl

/-- Installable additive left action; complex values are fixed. -/
@[instance_reducible]
def polynomialGrowthGaloisAction (n : ℕ) :
    DistribMulAction (K ≃ₐ[ℚ] K) (PolynomialGrowthRationalFunctions K n) where
  smul σ f := polynomialGrowthGaloisAut n σ f
  one_smul f := by
    change polynomialGrowthGaloisAut n 1 f = f
    rw [map_one]
    rfl
  mul_smul σ τ f := by
    change polynomialGrowthGaloisAut n (σ * τ) f =
      polynomialGrowthGaloisAut n σ (polynomialGrowthGaloisAut n τ f)
    rw [map_mul]
    rfl
  smul_zero σ := map_zero (polynomialGrowthGaloisAut n σ)
  smul_add σ := map_add (polynomialGrowthGaloisAut n σ)

theorem polynomialGrowthGaloisAut_rightAction (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (g : AdelicGL K n) (f : PolynomialGrowthRationalFunctions K n) :
    polynomialGrowthGaloisAut n σ
        (polynomialGrowthRightAction K n (AdelicGLTransport.adelicAut n (σ⁻¹) g) f) =
      polynomialGrowthRightAction K n g (polynomialGrowthGaloisAut n σ f) :=
  polynomialGrowthEquiv_rightAction n σ.toRingEquiv.symm g f

@[simp] theorem hasFiniteLevel_polynomialGrowthGaloisAut_iff (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : PolynomialGrowthRationalFunctions K n) :
    HasFiniteLevel K n (polynomialGrowthGaloisAut n σ f).val ↔ HasFiniteLevel K n f.val :=
  hasFiniteLevel_arithmeticComap_iff n σ.toRingEquiv.symm f.val

@[simp] theorem polynomialGrowthGaloisAut_mem_centralCharacter_iff (n : ℕ)
    (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K) (f : PolynomialGrowthRationalFunctions K n) :
    (polynomialGrowthGaloisAut n σ f).val ∈
        (centralCharacterSubrepresentation K n (HeckeCharacter.galoisAut σ χ)).toSubmodule ↔
      f.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  galoisAut_mem_centralCharacter_iff n σ χ f.val

/-- Inverse arithmetic pullback on this actual growth space. -/
def smoothPolynomialGrowthGaloisAut (n : ℕ) : (K ≃ₐ[ℚ] K) →*
    ((smoothPolynomialGrowthSubrepresentation K n).toSubmodule ≃L[ℂ] (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) where
  toFun σ := smoothPolynomialGrowthEquiv n σ.toRingEquiv.symm
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact smoothPolynomialGrowthEquiv_refl n f
  map_mul' σ τ := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact smoothPolynomialGrowthEquiv_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f

@[simp] theorem smoothPolynomialGrowthGaloisAut_val (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    (smoothPolynomialGrowthGaloisAut n σ f).val = galoisAut n σ f.val := rfl

@[simp] theorem evaluate_smoothPolynomialGrowthGaloisAut (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) (x : AdelicGL K n) :
    evaluate K n (smoothPolynomialGrowthGaloisAut n σ f).val x =
      evaluate K n f.val (AdelicGLTransport.adelicAut n (σ⁻¹) x) := rfl

/-- Installable additive left action; complex values are fixed. -/
@[instance_reducible]
def smoothPolynomialGrowthGaloisAction (n : ℕ) :
    DistribMulAction (K ≃ₐ[ℚ] K) ((smoothPolynomialGrowthSubrepresentation K n).toSubmodule) where
  smul σ f := smoothPolynomialGrowthGaloisAut n σ f
  one_smul f := by
    change smoothPolynomialGrowthGaloisAut n 1 f = f
    rw [map_one]
    rfl
  mul_smul σ τ f := by
    change smoothPolynomialGrowthGaloisAut n (σ * τ) f =
      smoothPolynomialGrowthGaloisAut n σ (smoothPolynomialGrowthGaloisAut n τ f)
    rw [map_mul]
    rfl
  smul_zero σ := map_zero (smoothPolynomialGrowthGaloisAut n σ)
  smul_add σ := map_add (smoothPolynomialGrowthGaloisAut n σ)

theorem smoothPolynomialGrowthGaloisAut_rightAction (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (g : AdelicGL K n) (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    smoothPolynomialGrowthGaloisAut n σ
        ((smoothPolynomialGrowthSubrepresentation K n).toRepresentation (AdelicGLTransport.adelicAut n (σ⁻¹) g) f) =
      (smoothPolynomialGrowthSubrepresentation K n).toRepresentation g (smoothPolynomialGrowthGaloisAut n σ f) :=
  smoothPolynomialGrowthEquiv_rightAction n σ.toRingEquiv.symm g f

@[simp] theorem hasFiniteLevel_smoothPolynomialGrowthGaloisAut_iff (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    HasFiniteLevel K n (smoothPolynomialGrowthGaloisAut n σ f).val ↔ HasFiniteLevel K n f.val :=
  hasFiniteLevel_arithmeticComap_iff n σ.toRingEquiv.symm f.val

@[simp] theorem smoothPolynomialGrowthGaloisAut_mem_centralCharacter_iff (n : ℕ)
    (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K) (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    (smoothPolynomialGrowthGaloisAut n σ f).val ∈
        (centralCharacterSubrepresentation K n (HeckeCharacter.galoisAut σ χ)).toSubmodule ↔
      f.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  galoisAut_mem_centralCharacter_iff n σ χ f.val

/-- Inverse arithmetic pullback on this actual growth space. -/
def finiteSmoothPolynomialGrowthGaloisAut (n : ℕ) : (K ≃ₐ[ℚ] K) →*
    ((finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule ≃L[ℂ] (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) where
  toFun σ := finiteSmoothPolynomialGrowthEquiv n σ.toRingEquiv.symm
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact finiteSmoothPolynomialGrowthEquiv_refl n f
  map_mul' σ τ := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact finiteSmoothPolynomialGrowthEquiv_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f

@[simp] theorem finiteSmoothPolynomialGrowthGaloisAut_val (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    (finiteSmoothPolynomialGrowthGaloisAut n σ f).val = galoisAut n σ f.val := rfl

@[simp] theorem evaluate_finiteSmoothPolynomialGrowthGaloisAut (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) (x : AdelicGL K n) :
    evaluate K n (finiteSmoothPolynomialGrowthGaloisAut n σ f).val x =
      evaluate K n f.val (AdelicGLTransport.adelicAut n (σ⁻¹) x) := rfl

/-- Installable additive left action; complex values are fixed. -/
@[instance_reducible]
def finiteSmoothPolynomialGrowthGaloisAction (n : ℕ) :
    DistribMulAction (K ≃ₐ[ℚ] K) ((finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) where
  smul σ f := finiteSmoothPolynomialGrowthGaloisAut n σ f
  one_smul f := by
    change finiteSmoothPolynomialGrowthGaloisAut n 1 f = f
    rw [map_one]
    rfl
  mul_smul σ τ f := by
    change finiteSmoothPolynomialGrowthGaloisAut n (σ * τ) f =
      finiteSmoothPolynomialGrowthGaloisAut n σ (finiteSmoothPolynomialGrowthGaloisAut n τ f)
    rw [map_mul]
    rfl
  smul_zero σ := map_zero (finiteSmoothPolynomialGrowthGaloisAut n σ)
  smul_add σ := map_add (finiteSmoothPolynomialGrowthGaloisAut n σ)

theorem finiteSmoothPolynomialGrowthGaloisAut_rightAction (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (g : AdelicGL K n) (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    finiteSmoothPolynomialGrowthGaloisAut n σ
        ((finiteSmoothPolynomialGrowthSubrepresentation K n).toRepresentation (AdelicGLTransport.adelicAut n (σ⁻¹) g) f) =
      (finiteSmoothPolynomialGrowthSubrepresentation K n).toRepresentation g (finiteSmoothPolynomialGrowthGaloisAut n σ f) :=
  finiteSmoothPolynomialGrowthEquiv_rightAction n σ.toRingEquiv.symm g f

@[simp] theorem hasFiniteLevel_finiteSmoothPolynomialGrowthGaloisAut_iff (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    HasFiniteLevel K n (finiteSmoothPolynomialGrowthGaloisAut n σ f).val ↔ HasFiniteLevel K n f.val :=
  hasFiniteLevel_arithmeticComap_iff n σ.toRingEquiv.symm f.val

@[simp] theorem finiteSmoothPolynomialGrowthGaloisAut_mem_centralCharacter_iff (n : ℕ)
    (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K) (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    (finiteSmoothPolynomialGrowthGaloisAut n σ f).val ∈
        (centralCharacterSubrepresentation K n (HeckeCharacter.galoisAut σ χ)).toSubmodule ↔
      f.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  galoisAut_mem_centralCharacter_iff n σ χ f.val

/-- The stronger common-stabilizer inclusion commutes with the growth action. -/
theorem smoothPolynomialGrowthGaloisAut_finiteSmoothInclusion (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    smoothPolynomialGrowthGaloisAut n σ
        (Submodule.inclusion (finiteSmoothPolynomialGrowth_le_smoothPolynomialGrowth K n) f) =
      Submodule.inclusion (finiteSmoothPolynomialGrowth_le_smoothPolynomialGrowth K n)
        (finiteSmoothPolynomialGrowthGaloisAut n σ f) :=
  smoothPolynomialGrowthEquiv_finiteSmoothInclusion n σ.toRingEquiv.symm f

/-- Forgetting growth gives exactly the previously constructed smooth action. -/
theorem smoothPolynomialGrowthGaloisAut_forgetGrowth (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    smoothGaloisAut n σ ⟨f.val, f.property.1⟩ =
      ⟨(smoothPolynomialGrowthGaloisAut n σ f).val,
        (smoothPolynomialGrowthGaloisAut n σ f).property.1⟩ := by
  apply Subtype.ext
  rfl

theorem finiteSmoothPolynomialGrowthGaloisAut_forgetGrowth (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    finiteSmoothGaloisAut n σ ⟨f.val, f.property.1⟩ =
      ⟨(finiteSmoothPolynomialGrowthGaloisAut n σ f).val,
        (finiteSmoothPolynomialGrowthGaloisAut n σ f).property.1⟩ := by
  apply Subtype.ext
  rfl

section CM
variable [NumberField.IsCMField K]

/-- Actual direct CM argument pullback on this growth space. -/
def polynomialGrowthComplexConj (n : ℕ) :
    PolynomialGrowthRationalFunctions K n ≃L[ℂ] PolynomialGrowthRationalFunctions K n :=
  polynomialGrowthEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv

@[simp] theorem polynomialGrowthComplexConj_val (n : ℕ) (f : PolynomialGrowthRationalFunctions K n) :
    (polynomialGrowthComplexConj n f).val = complexConj n f.val := rfl

@[simp] theorem evaluate_polynomialGrowthComplexConj (n : ℕ)
    (f : PolynomialGrowthRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (polynomialGrowthComplexConj n f).val x =
      evaluate K n f.val (CMConjugation.adelicConj K n x) :=
  evaluate_complexConj n f.val x

@[simp] theorem polynomialGrowthComplexConj_polynomialGrowthComplexConj (n : ℕ)
    (f : PolynomialGrowthRationalFunctions K n) :
    polynomialGrowthComplexConj n (polynomialGrowthComplexConj n f) = f := by
  apply Subtype.ext
  exact complexConj_complexConj n f.val

@[simp] theorem polynomialGrowthGaloisAut_complexConj (n : ℕ) (f : PolynomialGrowthRationalFunctions K n) :
    polynomialGrowthGaloisAut n ((NumberField.IsCMField.complexConj K).restrictScalars ℚ) f =
      polynomialGrowthComplexConj n f := by
  apply Subtype.ext
  exact galoisAut_complexConj n f.val

theorem polynomialGrowthComplexConj_rightAction (n : ℕ)
    (g : AdelicGL K n) (f : PolynomialGrowthRationalFunctions K n) :
    polynomialGrowthComplexConj n (polynomialGrowthRightAction K n (CMConjugation.adelicConj K n g) f) =
      polynomialGrowthRightAction K n g (polynomialGrowthComplexConj n f) := by
  have h := polynomialGrowthEquiv_rightAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv g f
  rwa [adelicEquiv_complexConj] at h

@[simp] theorem hasFiniteLevel_polynomialGrowthComplexConj_iff (n : ℕ) (f : PolynomialGrowthRationalFunctions K n) :
    HasFiniteLevel K n (polynomialGrowthComplexConj n f).val ↔ HasFiniteLevel K n f.val :=
  hasFiniteLevel_complexConj_iff n f.val

/-- Uses invariance of the actual standard infinite compact under CM conjugation. -/
@[simp] theorem isStandardInfiniteFinite_polynomialGrowthComplexConj_iff (n : ℕ)
    (f : PolynomialGrowthRationalFunctions K n) :
    IsInfiniteFinite K n (standardInfiniteCompact K n) (polynomialGrowthComplexConj n f).val ↔
      IsInfiniteFinite K n (standardInfiniteCompact K n) f.val :=
  isStandardInfiniteFinite_complexConj_iff n f.val

@[simp] theorem polynomialGrowthComplexConj_mem_centralCharacter_iff (n : ℕ)
    (χ : HeckeCharacter K) (f : PolynomialGrowthRationalFunctions K n) :
    (polynomialGrowthComplexConj n f).val ∈
        (centralCharacterSubrepresentation K n χ.complexConj).toSubmodule ↔
      f.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  complexConj_mem_centralCharacter_iff n χ f.val

/-- Actual direct CM argument pullback on this growth space. -/
def smoothPolynomialGrowthComplexConj (n : ℕ) :
    (smoothPolynomialGrowthSubrepresentation K n).toSubmodule ≃L[ℂ] (smoothPolynomialGrowthSubrepresentation K n).toSubmodule :=
  smoothPolynomialGrowthEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv

@[simp] theorem smoothPolynomialGrowthComplexConj_val (n : ℕ) (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    (smoothPolynomialGrowthComplexConj n f).val = complexConj n f.val := rfl

@[simp] theorem evaluate_smoothPolynomialGrowthComplexConj (n : ℕ)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) (x : AdelicGL K n) :
    evaluate K n (smoothPolynomialGrowthComplexConj n f).val x =
      evaluate K n f.val (CMConjugation.adelicConj K n x) :=
  evaluate_complexConj n f.val x

@[simp] theorem smoothPolynomialGrowthComplexConj_smoothPolynomialGrowthComplexConj (n : ℕ)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    smoothPolynomialGrowthComplexConj n (smoothPolynomialGrowthComplexConj n f) = f := by
  apply Subtype.ext
  exact complexConj_complexConj n f.val

@[simp] theorem smoothPolynomialGrowthGaloisAut_complexConj (n : ℕ) (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    smoothPolynomialGrowthGaloisAut n ((NumberField.IsCMField.complexConj K).restrictScalars ℚ) f =
      smoothPolynomialGrowthComplexConj n f := by
  apply Subtype.ext
  exact galoisAut_complexConj n f.val

theorem smoothPolynomialGrowthComplexConj_rightAction (n : ℕ)
    (g : AdelicGL K n) (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    smoothPolynomialGrowthComplexConj n ((smoothPolynomialGrowthSubrepresentation K n).toRepresentation (CMConjugation.adelicConj K n g) f) =
      (smoothPolynomialGrowthSubrepresentation K n).toRepresentation g (smoothPolynomialGrowthComplexConj n f) := by
  have h := smoothPolynomialGrowthEquiv_rightAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv g f
  rwa [adelicEquiv_complexConj] at h

@[simp] theorem hasFiniteLevel_smoothPolynomialGrowthComplexConj_iff (n : ℕ) (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    HasFiniteLevel K n (smoothPolynomialGrowthComplexConj n f).val ↔ HasFiniteLevel K n f.val :=
  hasFiniteLevel_complexConj_iff n f.val

/-- Uses invariance of the actual standard infinite compact under CM conjugation. -/
@[simp] theorem isStandardInfiniteFinite_smoothPolynomialGrowthComplexConj_iff (n : ℕ)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    IsInfiniteFinite K n (standardInfiniteCompact K n) (smoothPolynomialGrowthComplexConj n f).val ↔
      IsInfiniteFinite K n (standardInfiniteCompact K n) f.val :=
  isStandardInfiniteFinite_complexConj_iff n f.val

@[simp] theorem smoothPolynomialGrowthComplexConj_mem_centralCharacter_iff (n : ℕ)
    (χ : HeckeCharacter K) (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    (smoothPolynomialGrowthComplexConj n f).val ∈
        (centralCharacterSubrepresentation K n χ.complexConj).toSubmodule ↔
      f.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  complexConj_mem_centralCharacter_iff n χ f.val

/-- Actual direct CM argument pullback on this growth space. -/
def finiteSmoothPolynomialGrowthComplexConj (n : ℕ) :
    (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule ≃L[ℂ] (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule :=
  finiteSmoothPolynomialGrowthEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv

@[simp] theorem finiteSmoothPolynomialGrowthComplexConj_val (n : ℕ) (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    (finiteSmoothPolynomialGrowthComplexConj n f).val = complexConj n f.val := rfl

@[simp] theorem evaluate_finiteSmoothPolynomialGrowthComplexConj (n : ℕ)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) (x : AdelicGL K n) :
    evaluate K n (finiteSmoothPolynomialGrowthComplexConj n f).val x =
      evaluate K n f.val (CMConjugation.adelicConj K n x) :=
  evaluate_complexConj n f.val x

@[simp] theorem finiteSmoothPolynomialGrowthComplexConj_finiteSmoothPolynomialGrowthComplexConj (n : ℕ)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    finiteSmoothPolynomialGrowthComplexConj n (finiteSmoothPolynomialGrowthComplexConj n f) = f := by
  apply Subtype.ext
  exact complexConj_complexConj n f.val

@[simp] theorem finiteSmoothPolynomialGrowthGaloisAut_complexConj (n : ℕ) (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    finiteSmoothPolynomialGrowthGaloisAut n ((NumberField.IsCMField.complexConj K).restrictScalars ℚ) f =
      finiteSmoothPolynomialGrowthComplexConj n f := by
  apply Subtype.ext
  exact galoisAut_complexConj n f.val

theorem finiteSmoothPolynomialGrowthComplexConj_rightAction (n : ℕ)
    (g : AdelicGL K n) (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    finiteSmoothPolynomialGrowthComplexConj n ((finiteSmoothPolynomialGrowthSubrepresentation K n).toRepresentation (CMConjugation.adelicConj K n g) f) =
      (finiteSmoothPolynomialGrowthSubrepresentation K n).toRepresentation g (finiteSmoothPolynomialGrowthComplexConj n f) := by
  have h := finiteSmoothPolynomialGrowthEquiv_rightAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv g f
  rwa [adelicEquiv_complexConj] at h

@[simp] theorem hasFiniteLevel_finiteSmoothPolynomialGrowthComplexConj_iff (n : ℕ) (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    HasFiniteLevel K n (finiteSmoothPolynomialGrowthComplexConj n f).val ↔ HasFiniteLevel K n f.val :=
  hasFiniteLevel_complexConj_iff n f.val

/-- Uses invariance of the actual standard infinite compact under CM conjugation. -/
@[simp] theorem isStandardInfiniteFinite_finiteSmoothPolynomialGrowthComplexConj_iff (n : ℕ)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    IsInfiniteFinite K n (standardInfiniteCompact K n) (finiteSmoothPolynomialGrowthComplexConj n f).val ↔
      IsInfiniteFinite K n (standardInfiniteCompact K n) f.val :=
  isStandardInfiniteFinite_complexConj_iff n f.val

@[simp] theorem finiteSmoothPolynomialGrowthComplexConj_mem_centralCharacter_iff (n : ℕ)
    (χ : HeckeCharacter K) (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    (finiteSmoothPolynomialGrowthComplexConj n f).val ∈
        (centralCharacterSubrepresentation K n χ.complexConj).toSubmodule ↔
      f.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  complexConj_mem_centralCharacter_iff n χ f.val

theorem smoothPolynomialGrowthComplexConj_finiteSmoothInclusion (n : ℕ)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    smoothPolynomialGrowthComplexConj n
        (Submodule.inclusion (finiteSmoothPolynomialGrowth_le_smoothPolynomialGrowth K n) f) =
      Submodule.inclusion (finiteSmoothPolynomialGrowth_le_smoothPolynomialGrowth K n)
        (finiteSmoothPolynomialGrowthComplexConj n f) :=
  smoothPolynomialGrowthEquiv_finiteSmoothInclusion n
    (NumberField.IsCMField.complexConj K).toRingEquiv f

theorem smoothPolynomialGrowthComplexConj_forgetGrowth (n : ℕ)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    smoothComplexConj n ⟨f.val, f.property.1⟩ =
      ⟨(smoothPolynomialGrowthComplexConj n f).val,
        (smoothPolynomialGrowthComplexConj n f).property.1⟩ := by
  apply Subtype.ext
  rfl

theorem finiteSmoothPolynomialGrowthComplexConj_forgetGrowth (n : ℕ)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    finiteSmoothComplexConj n ⟨f.val, f.property.1⟩ =
      ⟨(finiteSmoothPolynomialGrowthComplexConj n f).val,
        (finiteSmoothPolynomialGrowthComplexConj n f).property.1⟩ := by
  apply Subtype.ext
  rfl

end CM
end Langlands.Automorphic.ContinuousRationalFunctions
