import Langlands.Automorphic.CenterFiniteArithmeticTransport
import Langlands.Automorphic.SmoothArithmeticActions
import Langlands.Automorphic.FiniteDifferential

/-! # Arithmetic actions on actual simultaneous center-finite adelic functions -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ContinuousRationalFunctions

open Langlands.Global AdelicGLTransport ArchimedeanLieTransport

variable {K : Type uK} [Field K] [NumberField K]

/-- Inverse arithmetic pullback on the actual simultaneous center-finite space. -/
def centerFiniteSmoothGaloisAut (n : ℕ) : (K ≃ₐ[ℚ] K) →*
    (CenterFiniteSmoothRationalFunctions K n ≃L[ℂ] CenterFiniteSmoothRationalFunctions K n) where
  toFun σ := centerFiniteSmoothEquiv n σ.toRingEquiv.symm
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact centerFiniteSmoothEquiv_refl n f
  map_mul' σ τ := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact centerFiniteSmoothEquiv_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f

@[simp] theorem centerFiniteSmoothGaloisAut_val (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : CenterFiniteSmoothRationalFunctions K n) :
    (centerFiniteSmoothGaloisAut n σ f).val = smoothGaloisAut n σ f.val := rfl

@[simp] theorem evaluate_centerFiniteSmoothGaloisAut (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : CenterFiniteSmoothRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (centerFiniteSmoothGaloisAut n σ f).val.val x =
      evaluate K n f.val.val (AdelicGLTransport.adelicAut n (σ⁻¹) x) := rfl

set_option maxHeartbeats 1000000 in
/-- Installable additive left action, with unchanged complex values. -/
@[instance_reducible]
def centerFiniteSmoothGaloisAction (n : ℕ) :
    DistribMulAction (K ≃ₐ[ℚ] K) (CenterFiniteSmoothRationalFunctions K n) where
  smul σ f := centerFiniteSmoothGaloisAut n σ f
  one_smul f := by
    change centerFiniteSmoothGaloisAut n 1 f = f
    rw [map_one]
    rfl
  mul_smul σ τ f := by
    change centerFiniteSmoothGaloisAut n (σ * τ) f =
      centerFiniteSmoothGaloisAut n σ (centerFiniteSmoothGaloisAut n τ f)
    exact centerFiniteSmoothEquiv_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f
  smul_zero σ := map_zero (centerFiniteSmoothGaloisAut n σ)
  smul_add σ := map_add (centerFiniteSmoothGaloisAut n σ)

@[simp] theorem hasFiniteLevel_centerFiniteSmoothGaloisAut_iff (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : CenterFiniteSmoothRationalFunctions K n) :
    HasFiniteLevel K n (centerFiniteSmoothGaloisAut n σ f).val.val ↔
      HasFiniteLevel K n f.val.val :=
  hasFiniteLevel_arithmeticComap_iff n σ.toRingEquiv.symm f.val.val

@[simp] theorem centerFiniteSmoothGaloisAut_mem_centralCharacter_iff (n : ℕ)
    (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K) (f : CenterFiniteSmoothRationalFunctions K n) :
    (centerFiniteSmoothGaloisAut n σ f).val.val ∈
        (centralCharacterSubrepresentation K n (HeckeCharacter.galoisAut σ χ)).toSubmodule ↔
      f.val.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  galoisAut_mem_centralCharacter_iff n σ χ f.val.val

/-- Inverse arithmetic pullback on the actual simultaneous center-finite space. -/
def centerFiniteFiniteSmoothGaloisAut (n : ℕ) : (K ≃ₐ[ℚ] K) →*
    (CenterFiniteFiniteSmoothRationalFunctions K n ≃L[ℂ] CenterFiniteFiniteSmoothRationalFunctions K n) where
  toFun σ := centerFiniteFiniteSmoothEquiv n σ.toRingEquiv.symm
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact centerFiniteFiniteSmoothEquiv_refl n f
  map_mul' σ τ := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact centerFiniteFiniteSmoothEquiv_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f

@[simp] theorem centerFiniteFiniteSmoothGaloisAut_val (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    (centerFiniteFiniteSmoothGaloisAut n σ f).val = finiteSmoothGaloisAut n σ f.val := rfl

@[simp] theorem evaluate_centerFiniteFiniteSmoothGaloisAut (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (centerFiniteFiniteSmoothGaloisAut n σ f).val.val x =
      evaluate K n f.val.val (AdelicGLTransport.adelicAut n (σ⁻¹) x) := rfl

set_option maxHeartbeats 1000000 in
/-- Installable additive left action, with unchanged complex values. -/
@[instance_reducible]
def centerFiniteFiniteSmoothGaloisAction (n : ℕ) :
    DistribMulAction (K ≃ₐ[ℚ] K) (CenterFiniteFiniteSmoothRationalFunctions K n) where
  smul σ f := centerFiniteFiniteSmoothGaloisAut n σ f
  one_smul f := by
    change centerFiniteFiniteSmoothGaloisAut n 1 f = f
    rw [map_one]
    rfl
  mul_smul σ τ f := by
    change centerFiniteFiniteSmoothGaloisAut n (σ * τ) f =
      centerFiniteFiniteSmoothGaloisAut n σ (centerFiniteFiniteSmoothGaloisAut n τ f)
    exact centerFiniteFiniteSmoothEquiv_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f
  smul_zero σ := map_zero (centerFiniteFiniteSmoothGaloisAut n σ)
  smul_add σ := map_add (centerFiniteFiniteSmoothGaloisAut n σ)

@[simp] theorem hasFiniteLevel_centerFiniteFiniteSmoothGaloisAut_iff (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    HasFiniteLevel K n (centerFiniteFiniteSmoothGaloisAut n σ f).val.val ↔
      HasFiniteLevel K n f.val.val :=
  hasFiniteLevel_arithmeticComap_iff n σ.toRingEquiv.symm f.val.val

@[simp] theorem centerFiniteFiniteSmoothGaloisAut_mem_centralCharacter_iff (n : ℕ)
    (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K) (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    (centerFiniteFiniteSmoothGaloisAut n σ f).val.val ∈
        (centralCharacterSubrepresentation K n (HeckeCharacter.galoisAut σ χ)).toSubmodule ↔
      f.val.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  galoisAut_mem_centralCharacter_iff n σ χ f.val.val

theorem centerFiniteSmoothGaloisAut_finiteRightAction (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (d : FiniteAdelicGL K n) (f : CenterFiniteSmoothRationalFunctions K n) :
    centerFiniteSmoothGaloisAut n σ
        (centerFiniteSmoothFiniteRightAction K n (finiteEquiv n σ.toRingEquiv.symm d) f) =
      centerFiniteSmoothFiniteRightAction K n d (centerFiniteSmoothGaloisAut n σ f) :=
  centerFiniteSmoothEquiv_finiteRightAction n σ.toRingEquiv.symm d f

/-- One common ideal transforms by arithmetic preimage under the actual center equivalence. -/
theorem centerFamilyAnnihilator_centerFiniteSmoothGaloisAut (n : ℕ)
    (σ : K ≃ₐ[ℚ] K) (f : CenterFiniteSmoothRationalFunctions K n) :
    centerFamilyAnnihilator K n
        (smoothSliceFamily K n (centerFiniteSmoothGaloisAut n σ f).val) =
      Ideal.comap (centerEquiv n σ.toRingEquiv.symm).toRingHom
        (centerFamilyAnnihilator K n (smoothSliceFamily K n f.val)) :=
  centerFamilyAnnihilator_smoothEquiv n σ.toRingEquiv.symm f.val

/-- Finite covariance on the actual space with a common open finite stabilizer. -/
theorem centerFiniteFiniteSmoothEquiv_finiteRightAction (n : ℕ) (e : K ≃+* K)
    (d : FiniteAdelicGL K n) (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothEquiv n e
        (centerFiniteFiniteSmoothRightAction K n (finiteEquiv n e d) f) =
      centerFiniteFiniteSmoothRightAction K n d (centerFiniteFiniteSmoothEquiv n e f) := by
  apply Subtype.ext
  change finiteSmoothEquiv n e
      (finiteSmoothRightAction K n (AdelicGL.ofFinite K n (finiteEquiv n e d)) f.val) =
    finiteSmoothRightAction K n (AdelicGL.ofFinite K n d) (finiteSmoothEquiv n e f.val)
  rw [← adelicEquiv_ofFinite]
  exact finiteSmoothEquiv_rightAction n e _ f.val

theorem centerFiniteFiniteSmoothGaloisAut_finiteRightAction (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (d : FiniteAdelicGL K n) (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothGaloisAut n σ
        (centerFiniteFiniteSmoothRightAction K n (finiteEquiv n σ.toRingEquiv.symm d) f) =
      centerFiniteFiniteSmoothRightAction K n d (centerFiniteFiniteSmoothGaloisAut n σ f) :=
  centerFiniteFiniteSmoothEquiv_finiteRightAction n σ.toRingEquiv.symm d f

/-- The Galois action intertwines the actual restricted differential operators. -/
theorem centerFiniteFiniteSmoothGaloisAut_envelopingAction (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothGaloisAut n σ
        (centerFiniteEnvelopingAction K n (envelopingEquiv n σ.toRingEquiv.symm u) f) =
      centerFiniteEnvelopingAction K n u (centerFiniteFiniteSmoothGaloisAut n σ f) :=
  centerFiniteFiniteSmoothEquiv_envelopingAction n σ.toRingEquiv.symm u f

section CM
variable [NumberField.IsCMField K]

/-- Direct argument conjugation by the genuine arithmetic CM involution. -/
def centerFiniteSmoothComplexConj (n : ℕ) :
    CenterFiniteSmoothRationalFunctions K n ≃L[ℂ] CenterFiniteSmoothRationalFunctions K n :=
  centerFiniteSmoothEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv

@[simp] theorem centerFiniteSmoothComplexConj_val (n : ℕ)
    (f : CenterFiniteSmoothRationalFunctions K n) :
    (centerFiniteSmoothComplexConj n f).val = smoothComplexConj n f.val := rfl

@[simp] theorem evaluate_centerFiniteSmoothComplexConj (n : ℕ)
    (f : CenterFiniteSmoothRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (centerFiniteSmoothComplexConj n f).val.val x =
      evaluate K n f.val.val (CMConjugation.adelicConj K n x) :=
  evaluate_complexConj n f.val.val x

@[simp] theorem centerFiniteSmoothComplexConj_centerFiniteSmoothComplexConj (n : ℕ)
    (f : CenterFiniteSmoothRationalFunctions K n) :
    centerFiniteSmoothComplexConj n (centerFiniteSmoothComplexConj n f) = f := by
  apply Subtype.ext
  exact smoothComplexConj_smoothComplexConj n f.val

@[simp] theorem centerFiniteSmoothGaloisAut_complexConj (n : ℕ)
    (f : CenterFiniteSmoothRationalFunctions K n) :
    centerFiniteSmoothGaloisAut n ((NumberField.IsCMField.complexConj K).restrictScalars ℚ) f =
      centerFiniteSmoothComplexConj n f := by
  apply Subtype.ext
  exact smoothGaloisAut_complexConj n f.val

theorem centerFiniteSmoothComplexConj_finiteRightAction (n : ℕ)
    (d : FiniteAdelicGL K n) (f : CenterFiniteSmoothRationalFunctions K n) :
    centerFiniteSmoothComplexConj n (centerFiniteSmoothFiniteRightAction K n (CMConjugation.finiteConj K n d) f) =
      centerFiniteSmoothFiniteRightAction K n d (centerFiniteSmoothComplexConj n f) := by
  have h := centerFiniteSmoothEquiv_finiteRightAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv d f
  rwa [finiteEquiv_complexConj] at h

@[simp] theorem hasFiniteLevel_centerFiniteSmoothComplexConj_iff (n : ℕ)
    (f : CenterFiniteSmoothRationalFunctions K n) :
    HasFiniteLevel K n (centerFiniteSmoothComplexConj n f).val.val ↔
      HasFiniteLevel K n f.val.val :=
  hasFiniteLevel_complexConj_iff n f.val.val

/-- Uses the proved invariance of the actual standard infinite compact under CM conjugation. -/
@[simp] theorem isStandardInfiniteFinite_centerFiniteSmoothComplexConj_iff (n : ℕ)
    (f : CenterFiniteSmoothRationalFunctions K n) :
    IsInfiniteFinite K n (standardInfiniteCompact K n) (centerFiniteSmoothComplexConj n f).val.val ↔
      IsInfiniteFinite K n (standardInfiniteCompact K n) f.val.val :=
  isStandardInfiniteFinite_complexConj_iff n f.val.val

@[simp] theorem centerFiniteSmoothComplexConj_mem_centralCharacter_iff (n : ℕ)
    (χ : HeckeCharacter K) (f : CenterFiniteSmoothRationalFunctions K n) :
    (centerFiniteSmoothComplexConj n f).val.val ∈
        (centralCharacterSubrepresentation K n χ.complexConj).toSubmodule ↔
      f.val.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  complexConj_mem_centralCharacter_iff n χ f.val.val

/-- Direct argument conjugation by the genuine arithmetic CM involution. -/
def centerFiniteFiniteSmoothComplexConj (n : ℕ) :
    CenterFiniteFiniteSmoothRationalFunctions K n ≃L[ℂ] CenterFiniteFiniteSmoothRationalFunctions K n :=
  centerFiniteFiniteSmoothEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv

@[simp] theorem centerFiniteFiniteSmoothComplexConj_val (n : ℕ)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    (centerFiniteFiniteSmoothComplexConj n f).val = finiteSmoothComplexConj n f.val := rfl

@[simp] theorem evaluate_centerFiniteFiniteSmoothComplexConj (n : ℕ)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (centerFiniteFiniteSmoothComplexConj n f).val.val x =
      evaluate K n f.val.val (CMConjugation.adelicConj K n x) :=
  evaluate_complexConj n f.val.val x

@[simp] theorem centerFiniteFiniteSmoothComplexConj_centerFiniteFiniteSmoothComplexConj (n : ℕ)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothComplexConj n (centerFiniteFiniteSmoothComplexConj n f) = f := by
  apply Subtype.ext
  exact finiteSmoothComplexConj_finiteSmoothComplexConj n f.val

@[simp] theorem centerFiniteFiniteSmoothGaloisAut_complexConj (n : ℕ)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothGaloisAut n ((NumberField.IsCMField.complexConj K).restrictScalars ℚ) f =
      centerFiniteFiniteSmoothComplexConj n f := by
  apply Subtype.ext
  exact finiteSmoothGaloisAut_complexConj n f.val

theorem centerFiniteFiniteSmoothComplexConj_finiteRightAction (n : ℕ)
    (d : FiniteAdelicGL K n) (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothComplexConj n (centerFiniteFiniteSmoothRightAction K n (CMConjugation.finiteConj K n d) f) =
      centerFiniteFiniteSmoothRightAction K n d (centerFiniteFiniteSmoothComplexConj n f) := by
  have h := centerFiniteFiniteSmoothEquiv_finiteRightAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv d f
  rwa [finiteEquiv_complexConj] at h

@[simp] theorem hasFiniteLevel_centerFiniteFiniteSmoothComplexConj_iff (n : ℕ)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    HasFiniteLevel K n (centerFiniteFiniteSmoothComplexConj n f).val.val ↔
      HasFiniteLevel K n f.val.val :=
  hasFiniteLevel_complexConj_iff n f.val.val

/-- Uses the proved invariance of the actual standard infinite compact under CM conjugation. -/
@[simp] theorem isStandardInfiniteFinite_centerFiniteFiniteSmoothComplexConj_iff (n : ℕ)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    IsInfiniteFinite K n (standardInfiniteCompact K n) (centerFiniteFiniteSmoothComplexConj n f).val.val ↔
      IsInfiniteFinite K n (standardInfiniteCompact K n) f.val.val :=
  isStandardInfiniteFinite_complexConj_iff n f.val.val

@[simp] theorem centerFiniteFiniteSmoothComplexConj_mem_centralCharacter_iff (n : ℕ)
    (χ : HeckeCharacter K) (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    (centerFiniteFiniteSmoothComplexConj n f).val.val ∈
        (centralCharacterSubrepresentation K n χ.complexConj).toSubmodule ↔
      f.val.val ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  complexConj_mem_centralCharacter_iff n χ f.val.val

/-- CM pullback intertwines the actual restricted enveloping differential action. -/
theorem centerFiniteFiniteSmoothComplexConj_envelopingAction (n : ℕ)
    (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothComplexConj n
        (centerFiniteEnvelopingAction K n
          (envelopingEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv u) f) =
      centerFiniteEnvelopingAction K n u (centerFiniteFiniteSmoothComplexConj n f) :=
  centerFiniteFiniteSmoothEquiv_envelopingAction n
    (NumberField.IsCMField.complexConj K).toRingEquiv u f

/-- The CM action transports the single ideal that annihilates the entire family. -/
theorem centerFamilyAnnihilator_centerFiniteSmoothComplexConj (n : ℕ)
    (f : CenterFiniteSmoothRationalFunctions K n) :
    centerFamilyAnnihilator K n
        (smoothSliceFamily K n (centerFiniteSmoothComplexConj n f).val) =
      Ideal.comap (centerEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv).toRingHom
        (centerFamilyAnnihilator K n (smoothSliceFamily K n f.val)) :=
  centerFamilyAnnihilator_smoothEquiv n
    (NumberField.IsCMField.complexConj K).toRingEquiv f.val

end CM
end Langlands.Automorphic.ContinuousRationalFunctions
