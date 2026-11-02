import Langlands.Automorphic.FiniteOrderHeckeLocalModels
import Langlands.Automorphic.FiniteDeterminantTail
import Langlands.Automorphic.TensorPresentation
import Langlands.Representation.RestrictedTensor.Scalars

/-! # Actual restricted tensor presentations of finite-order automorphic Hecke lines -/

noncomputable section
open scoped Classical TensorProduct

universe uF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.FiniteOrderHeckeRealization

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor
open ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance heckeTensorPresentationGroup1 : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorPresentationGroup2 : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorPresentationGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorPresentationGroup4 : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance heckeTensorPresentationGroup5 : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorPresentationGroup6 : AddCommGroup (realization F n χ hχ).Space := Submodule.addCommGroup _

/-- The scalar-one references are fixed outside the actual full determinant tail. -/
theorem tensorReference_fixed (v : FinitePlace F)
    (hv : v ∉ χ.finiteDeterminantTail n hχ)
    (g : FiniteLocalGL F n v) (hg : g ∈ localIntegral F n v) :
    localModel F n χ v g (1 : ℂ) = 1 := by
  change (χ.finiteLocalDeterminant n v g : ℂ) * 1 = 1
  rw [χ.finiteLocalDeterminant_eq_one_outside_tail n hχ v hv g hg]
  simp only [Units.val_one, one_mul]

/-- The actual finite adelic tensor of local determinant-character lines is its
global finite determinant-character line. -/
def finiteTensorScalarEquiv :
    (tensorRepresentation F n (localModel F n χ)
      (χ.finiteDeterminantTail n hχ) (fun _ => (1 : ℂ))
      (tensorReference_fixed F n χ hχ)).Equiv (finiteModel F n χ) :=
  Representation.Equiv.mk
    (Langlands.RestrictedTensor.scalarEquiv ℂ (χ.finiteDeterminantTail n hχ))
    (fun g => by
      let H := fun v => (localIntegral F n v).toSubgroup
      let ψ := (χ.finiteRestrictedDeterminant n).toMonoidHom
      let E := χ.finiteDeterminantTail n hχ
      have htail : ∀ t ∈ tailReferenceSubgroup H E, ψ t = 1 :=
        χ.finiteDeterminantTail_trivial n hχ
      have hlocal :
          (fun v => Langlands.characterRepresentation (localCharacter H ψ v)) =
            localModel F n χ := by
        funext v
        rw [HeckeCharacter.localCharacter_finiteRestrictedDeterminant]
        rfl
      have hrepresentation :
          representation H (localModel F n χ) E (fun _ => (1 : ℂ))
              (tensorReference_fixed F n χ hχ) =
            representation H
              (fun v => Langlands.characterRepresentation (localCharacter H ψ v))
              E (fun _ => (1 : ℂ))
              (characterScalarReference_fixed ℂ H E ψ htail) := by
        congr 1
        exact hlocal.symm
      apply LinearMap.ext
      intro x
      change Langlands.RestrictedTensor.scalarEquiv ℂ E
          (representation H (localModel F n χ) E (fun _ => (1 : ℂ))
            (tensorReference_fixed F n χ hχ) (restrictedProductEquiv F n g) x) =
        (χ.finiteAdelicDeterminant n g : ℂ) *
          Langlands.RestrictedTensor.scalarEquiv ℂ E x
      rw [hrepresentation]
      have h := LinearMap.congr_fun
        ((characterScalarTensorEquiv ℂ H E ψ htail).isIntertwining'
          (restrictedProductEquiv F n g)) x
      change Langlands.RestrictedTensor.scalarEquiv ℂ E
          (representation H
            (fun v => Langlands.characterRepresentation (localCharacter H ψ v))
            E (fun _ => (1 : ℂ)) (characterScalarReference_fixed ℂ H E ψ htail)
            (restrictedProductEquiv F n g) x) =
        (χ.finiteRestrictedDeterminant n (restrictedProductEquiv F n g) : ℂ) *
          Langlands.RestrictedTensor.scalarEquiv ℂ E x at h
      rw [HeckeCharacter.finiteRestrictedDeterminant_apply] at h
      exact h)

@[simp]
theorem finiteTensorScalarEquiv_pure
    (S : Index (χ.finiteDeterminantTail n hχ)) (x : S.1 → ℂ) :
    finiteTensorScalarEquiv F n χ hχ
      (pure (χ.finiteDeterminantTail n hχ) (fun _ => (1 : ℂ)) S x) = ∏ v, x v :=
  Langlands.RestrictedTensor.scalarEquiv_pure ℂ _ S x

/-- A constructed presentation onto the prescribed actual finite form image. -/
def finiteTensorPresentation :
    FiniteTensorPresentation F n (localModel F n χ)
      (χ.finiteDeterminantTail n hχ) (fun _ => (1 : ℂ))
      (tensorReference_fixed F n χ hχ)
      (realization F n χ hχ).toFiniteRealization where
  reference_nonzero _ _ := one_ne_zero
  equiv := (finiteTensorScalarEquiv F n χ hχ).trans (finiteFormEquiv F n χ hχ)

/-- The form-valued tensor map is faithful and has exactly this actual line as image. -/
theorem finiteTensorPresentation_image :
    finiteRealizationImage F n (finiteTensorPresentation F n χ hχ).toMap =
      (realization F n χ hχ).toFiniteRealization :=
  (finiteTensorPresentation F n χ hχ).image_toMap

theorem finiteTensorPresentation_injective :
    Function.Injective (finiteTensorPresentation F n χ hχ).toMap :=
  (finiteTensorPresentation F n χ hχ).toMap_injective

@[simp]
theorem finiteTensorPresentation_toMap_pure
    (S : Index (χ.finiteDeterminantTail n hχ)) (x : S.1 → ℂ) :
    (finiteTensorPresentation F n χ hχ).toMap
        (pure (χ.finiteDeterminantTail n hχ) (fun _ => (1 : ℂ)) S x) =
      form F n χ hχ (∏ v, x v) := by
  change form F n χ hχ
    (finiteTensorScalarEquiv F n χ hχ
      (pure (χ.finiteDeterminantTail n hχ) (fun _ => (1 : ℂ)) S x)) = _
  rw [finiteTensorScalarEquiv_pure]

/-- Elementary restricted tensors represent the literal determinant-character functions. -/
theorem evaluate_finiteTensorPresentation_pure
    (S : Index (χ.finiteDeterminantTail n hχ)) (x : S.1 → ℂ) (a : AdelicGL F n) :
    evaluate F n
      (automorphicToContinuous F n
        ((finiteTensorPresentation F n χ hχ).toMap
          (pure (χ.finiteDeterminantTail n hχ) (fun _ => (1 : ℂ)) S x))) a =
      (χ.adelicDeterminant n a : ℂ) * ∏ v, x v := by
  rw [finiteTensorPresentation_toMap_pure, evaluate_form]

variable (v : FinitePlace F)

/-- A specific nonzero complementary tensor, including an empty complementary index type. -/
def tensorTailVector :
    Langlands.Global.FiniteAdelicGL.LocalTensorTail (K := ℂ) F
      (χ.finiteDeterminantTail n hχ) v (fun _ => (1 : ℂ)) :=
  (Langlands.RestrictedTensor.scalarEquiv ℂ
    (tailSet {v} (χ.finiteDeterminantTail n hχ))).symm 1

theorem tensorTailVector_ne_zero : tensorTailVector F n χ hχ v ≠ 0 := by
  intro h
  have he := congrArg
    (Langlands.RestrictedTensor.scalarEquiv ℂ
      (tailSet {v} (χ.finiteDeterminantTail n hχ))) h
  change Langlands.RestrictedTensor.scalarEquiv ℂ _
    ((Langlands.RestrictedTensor.scalarEquiv ℂ _).symm 1) =
      Langlands.RestrictedTensor.scalarEquiv ℂ _ 0 at he
  rw [LinearEquiv.apply_symm_apply] at he
  have hz := (Langlands.RestrictedTensor.scalarEquiv ℂ
    (tailSet {v} (χ.finiteDeterminantTail n hχ))).toLinearMap.map_zero
  exact one_ne_zero (he.trans hz)

/-- The constructed nonzero slice has the same local class as the whole actual line. -/
theorem tensorSlice_isoClass :
    ((finiteTensorPresentation F n χ hχ).slice v (tensorTailVector F n χ hχ v)).isoClass =
      ((realization F n χ hχ).toFiniteRealization.toLocal F n v).isoClass :=
  (LocalRealization.isoClass_eq_iff _ _).mpr
    ⟨((finiteTensorPresentation F n χ hχ).sliceEquiv v
      (tensorTailVector F n χ hχ v) (tensorTailVector_ne_zero F n χ hχ v)).symm.trans
        (localFormEquiv F n χ hχ v)⟩

/-- Almost every constructed local slice has a nonzero integral-fixed vector. -/
theorem tensorSlice_exists_integral_fixed (hv : v ∉ χ.finiteDeterminantTail n hχ) :
    ∃ f : ((finiteTensorPresentation F n χ hχ).slice v
        (tensorTailVector F n χ hχ v)).Space,
      f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
        ((finiteTensorPresentation F n χ hχ).slice v
          (tensorTailVector F n χ hχ v)).representation g f = f :=
  FiniteTensorRealization.slice_exists_integral_fixed F n (localModel F n χ)
    (χ.finiteDeterminantTail n hχ) (fun _ => (1 : ℂ))
    (tensorReference_fixed F n χ hχ) (fun _ _ => one_ne_zero)
    (finiteTensorPresentation F n χ hχ).toMap
    (finiteTensorPresentation F n χ hχ).toMap_injective v hv
    (tensorTailVector F n χ hχ v) (tensorTailVector_ne_zero F n χ hχ v)

end Langlands.Automorphic.FiniteOrderHeckeRealization
