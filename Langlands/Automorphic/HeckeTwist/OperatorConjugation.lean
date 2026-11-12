import Langlands.Automorphic.DeterminantOperatorConjugation
import Langlands.Automorphic.HeckeTwist.DifferentialMultiplier
import Langlands.Automorphic.OperatorCore

/-! # Conjugation of the automorphic operator algebra by any Hecke multiplier

Conjugation by multiplication by `χ ∘ det`, for an arbitrary Hecke character `χ`, is an
automorphism of the concrete automorphic operator algebra. It scales finite and compact
translations by the determinant character and shifts differential operators by the
enveloping-algebra automorphism `heckeEnvelopingShift n χ`.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance heckeDeterminantConjugationRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeDeterminantConjugationContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeDeterminantConjugationFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- Pull an actual ambient operator back by determinant multiplication: `Mχ⁻¹ A Mχ`. -/
def finiteSmoothHeckeDeterminantConjugation (χ : HeckeCharacter F) :
    FiniteSmoothEnd F n ≃ₐ[ℂ] FiniteSmoothEnd F n :=
  (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).toLinearEquiv.symm.conjAlgEquiv ℂ

@[simp]
theorem finiteSmoothHeckeDeterminantConjugation_apply
    (χ : HeckeCharacter F) (a : FiniteSmoothEnd F n)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothHeckeDeterminantConjugation n χ a f =
      (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).symm
        (a (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f)) := rfl

@[simp]
theorem finiteSmoothHeckeDeterminantConjugation_finite
    (χ : HeckeCharacter F) (d : FiniteAdelicGL F n) :
    finiteSmoothHeckeDeterminantConjugation n χ (finiteSmoothFiniteRightAction F n d) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        finiteSmoothFiniteRightAction F n d := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothHeckeDeterminantConjugation_apply]
  change (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).symm
      (finiteSmoothRightAction F n (AdelicGL.ofFinite F n d)
        (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f)) = _
  rw [FiniteSmoothRationalFunctions.heckeDeterminantMultiplier_rightAction,
    map_smul, ContinuousLinearEquiv.symm_apply_apply]
  rfl

@[simp]
theorem finiteSmoothHeckeDeterminantConjugation_compact
    (χ : HeckeCharacter F) (k : standardInfiniteCompact F n) :
    finiteSmoothHeckeDeterminantConjugation n χ (finiteSmoothCompactRightAction F n k) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) •
        finiteSmoothCompactRightAction F n k := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothHeckeDeterminantConjugation_apply]
  change (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).symm
      (finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val)
        (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f)) = _
  rw [FiniteSmoothRationalFunctions.heckeDeterminantMultiplier_rightAction,
    map_smul, ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- Conjugating a differential operator gives the differential operator of the shifted
enveloping-algebra element. -/
@[simp]
theorem finiteSmoothHeckeDeterminantConjugation_differential
    (χ : HeckeCharacter F)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    finiteSmoothHeckeDeterminantConjugation n χ (finiteSmoothEnvelopingAction F n a) =
      finiteSmoothEnvelopingAction F n (heckeEnvelopingShift n χ a) := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothHeckeDeterminantConjugation_apply,
    finiteSmoothEnvelopingAction_heckeDeterminantMultiplier,
    ContinuousLinearEquiv.symm_apply_apply]

private theorem finiteSmoothDeterminantConjugation_mem
    (χ : HeckeCharacter F) (a : FiniteSmoothEnd F n)
    (ha : a ∈ automorphicOperatorAlgebra F n) :
    finiteSmoothHeckeDeterminantConjugation n χ a ∈ automorphicOperatorAlgebra F n := by
  refine Algebra.adjoin_induction
    (p := fun a _ => finiteSmoothHeckeDeterminantConjugation n χ a ∈
      automorphicOperatorAlgebra F n) ?_ ?_ ?_ ?_ ha
  · rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩)
    · rw [finiteSmoothHeckeDeterminantConjugation_finite]
      exact (automorphicOperatorAlgebra F n).smul_mem
        (Algebra.subset_adjoin (Or.inl (Or.inl ⟨d, rfl⟩))) _
    · rw [finiteSmoothHeckeDeterminantConjugation_compact]
      exact (automorphicOperatorAlgebra F n).smul_mem
        (Algebra.subset_adjoin (Or.inl (Or.inr ⟨k, rfl⟩))) _
    · rw [finiteSmoothHeckeDeterminantConjugation_differential]
      exact Algebra.subset_adjoin (Or.inr ⟨heckeEnvelopingShift n χ u, rfl⟩)
  · intro c
    rw [AlgEquiv.commutes]
    exact (automorphicOperatorAlgebra F n).algebraMap_mem c
  · intro a b ha hb hca hcb
    rw [map_add]
    exact (automorphicOperatorAlgebra F n).add_mem hca hcb
  · intro a b ha hb hca hcb
    rw [map_mul]
    exact (automorphicOperatorAlgebra F n).mul_mem hca hcb

private theorem finiteSmoothDeterminantConjugation_inv
    (χ : HeckeCharacter F) :
    finiteSmoothHeckeDeterminantConjugation n χ⁻¹  =
      (finiteSmoothHeckeDeterminantConjugation n χ).symm := by
  apply AlgEquiv.ext
  intro a
  apply LinearMap.ext
  intro f
  rfl

/-- An automorphism of the existing concrete operator algebra, with no free presentation. -/
def heckeDeterminantOperatorConjugation (χ : HeckeCharacter F) :
    automorphicOperatorAlgebra F n ≃ₐ[ℂ] automorphicOperatorAlgebra F n where
  toFun a := ⟨finiteSmoothHeckeDeterminantConjugation n χ a.val,
    finiteSmoothDeterminantConjugation_mem n χ a.val a.property⟩
  invFun a := ⟨finiteSmoothHeckeDeterminantConjugation n χ⁻¹  a.val,
    finiteSmoothDeterminantConjugation_mem n χ⁻¹  a.val a.property⟩
  left_inv a := by
    apply Subtype.ext
    change finiteSmoothHeckeDeterminantConjugation n χ⁻¹
      (finiteSmoothHeckeDeterminantConjugation n χ a.val) = a.val
    rw [finiteSmoothDeterminantConjugation_inv n χ, AlgEquiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    change finiteSmoothHeckeDeterminantConjugation n χ
      (finiteSmoothHeckeDeterminantConjugation n χ⁻¹  a.val) = a.val
    rw [finiteSmoothDeterminantConjugation_inv n χ, AlgEquiv.apply_symm_apply]
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  commutes' c := Subtype.ext (AlgEquiv.commutes _ c)

@[simp]
theorem heckeDeterminantOperatorConjugation_val
    (χ : HeckeCharacter F) (a : automorphicOperatorAlgebra F n) :
    (heckeDeterminantOperatorConjugation n χ a).val =
      finiteSmoothHeckeDeterminantConjugation n χ a.val := rfl

@[simp]
theorem heckeDeterminantOperatorConjugation_finite
    (χ : HeckeCharacter F) (d : FiniteAdelicGL F n) :
    heckeDeterminantOperatorConjugation n χ (finiteOperator F n d) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) • finiteOperator F n d := by
  apply Subtype.ext
  exact finiteSmoothHeckeDeterminantConjugation_finite n χ d

@[simp]
theorem heckeDeterminantOperatorConjugation_compact
    (χ : HeckeCharacter F) (k : standardInfiniteCompact F n) :
    heckeDeterminantOperatorConjugation n χ (compactOperator F n k) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) • compactOperator F n k := by
  apply Subtype.ext
  exact finiteSmoothHeckeDeterminantConjugation_compact n χ k

@[simp]
theorem heckeDeterminantOperatorConjugation_differential
    (χ : HeckeCharacter F)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    heckeDeterminantOperatorConjugation n χ (differentialOperator F n a) =
      differentialOperator F n (heckeEnvelopingShift n χ a) := by
  apply Subtype.ext
  exact finiteSmoothHeckeDeterminantConjugation_differential n χ a

theorem heckeDeterminantOperatorConjugation_inv
    (χ : HeckeCharacter F) :
    heckeDeterminantOperatorConjugation n χ⁻¹  =
      (heckeDeterminantOperatorConjugation n χ).symm := by
  apply AlgEquiv.ext
  intro a
  rfl

/-- The actual whole-algebra covariance identity used to descend to invariant cores. -/
theorem operatorAction_heckeDeterminantMultiplier
    (χ : HeckeCharacter F)
    (a : automorphicOperatorAlgebra F n) (f : FiniteSmoothRationalFunctions F n) :
    a.val (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f) =
      FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ
        ((heckeDeterminantOperatorConjugation n χ a).val f) := by
  change a.val (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f) =
    FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ
      ((FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).symm
        (a.val (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f)))
  rw [ContinuousLinearEquiv.apply_symm_apply]

end Langlands.Automorphic
