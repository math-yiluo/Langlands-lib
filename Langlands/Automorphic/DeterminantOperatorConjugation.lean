import Langlands.Automorphic.DifferentialDeterminantMultiplier
import Langlands.Automorphic.OperatorCore

/-! # Actual determinant conjugation of the concrete automorphic operator algebra -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance determinantConjugationRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance determinantConjugationContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance determinantConjugationFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- Pull an actual ambient operator back by determinant multiplication: `Mχ⁻¹ A Mχ`. -/
def finiteSmoothDeterminantConjugation (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    FiniteSmoothEnd F n ≃ₐ[ℂ] FiniteSmoothEnd F n :=
  (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).toLinearEquiv.symm.conjAlgEquiv ℂ

@[simp]
theorem finiteSmoothDeterminantConjugation_apply
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (a : FiniteSmoothEnd F n)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothDeterminantConjugation n χ hχ a f =
      (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).symm
        (a (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f)) := rfl

@[simp]
theorem finiteSmoothDeterminantConjugation_finite
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (d : FiniteAdelicGL F n) :
    finiteSmoothDeterminantConjugation n χ hχ (finiteSmoothFiniteRightAction F n d) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        finiteSmoothFiniteRightAction F n d := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothDeterminantConjugation_apply]
  change (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).symm
      (finiteSmoothRightAction F n (AdelicGL.ofFinite F n d)
        (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f)) = _
  rw [FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_rightAction,
    map_smul, ContinuousLinearEquiv.symm_apply_apply]
  rfl

@[simp]
theorem finiteSmoothDeterminantConjugation_compact
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (k : standardInfiniteCompact F n) :
    finiteSmoothDeterminantConjugation n χ hχ (finiteSmoothCompactRightAction F n k) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) •
        finiteSmoothCompactRightAction F n k := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothDeterminantConjugation_apply]
  change (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).symm
      (finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val)
        (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f)) = _
  rw [FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_rightAction,
    map_smul, ContinuousLinearEquiv.symm_apply_apply]
  rfl

@[simp]
theorem finiteSmoothDeterminantConjugation_differential
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    finiteSmoothDeterminantConjugation n χ hχ (finiteSmoothEnvelopingAction F n a) =
      finiteSmoothEnvelopingAction F n a := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothDeterminantConjugation_apply,
    finiteSmoothEnvelopingAction_determinantMultiplier,
    ContinuousLinearEquiv.symm_apply_apply]

private theorem finiteSmoothDeterminantConjugation_mem
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (a : FiniteSmoothEnd F n)
    (ha : a ∈ automorphicOperatorAlgebra F n) :
    finiteSmoothDeterminantConjugation n χ hχ a ∈ automorphicOperatorAlgebra F n := by
  refine Algebra.adjoin_induction
    (p := fun a _ => finiteSmoothDeterminantConjugation n χ hχ a ∈
      automorphicOperatorAlgebra F n) ?_ ?_ ?_ ?_ ha
  · rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩)
    · rw [finiteSmoothDeterminantConjugation_finite]
      exact (automorphicOperatorAlgebra F n).smul_mem
        (Algebra.subset_adjoin (Or.inl (Or.inl ⟨d, rfl⟩))) _
    · rw [finiteSmoothDeterminantConjugation_compact]
      exact (automorphicOperatorAlgebra F n).smul_mem
        (Algebra.subset_adjoin (Or.inl (Or.inr ⟨k, rfl⟩))) _
    · rw [finiteSmoothDeterminantConjugation_differential]
      exact Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)
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
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    finiteSmoothDeterminantConjugation n χ⁻¹ hχ.inv =
      (finiteSmoothDeterminantConjugation n χ hχ).symm := by
  apply AlgEquiv.ext
  intro a
  apply LinearMap.ext
  intro f
  rfl

/-- An automorphism of the existing concrete operator algebra, with no free presentation. -/
def determinantOperatorConjugation (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    automorphicOperatorAlgebra F n ≃ₐ[ℂ] automorphicOperatorAlgebra F n where
  toFun a := ⟨finiteSmoothDeterminantConjugation n χ hχ a.val,
    finiteSmoothDeterminantConjugation_mem n χ hχ a.val a.property⟩
  invFun a := ⟨finiteSmoothDeterminantConjugation n χ⁻¹ hχ.inv a.val,
    finiteSmoothDeterminantConjugation_mem n χ⁻¹ hχ.inv a.val a.property⟩
  left_inv a := by
    apply Subtype.ext
    change finiteSmoothDeterminantConjugation n χ⁻¹ hχ.inv
      (finiteSmoothDeterminantConjugation n χ hχ a.val) = a.val
    rw [finiteSmoothDeterminantConjugation_inv n χ hχ, AlgEquiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    change finiteSmoothDeterminantConjugation n χ hχ
      (finiteSmoothDeterminantConjugation n χ⁻¹ hχ.inv a.val) = a.val
    rw [finiteSmoothDeterminantConjugation_inv n χ hχ, AlgEquiv.apply_symm_apply]
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  commutes' c := Subtype.ext (AlgEquiv.commutes _ c)

@[simp]
theorem determinantOperatorConjugation_val
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (a : automorphicOperatorAlgebra F n) :
    (determinantOperatorConjugation n χ hχ a).val =
      finiteSmoothDeterminantConjugation n χ hχ a.val := rfl

@[simp]
theorem determinantOperatorConjugation_finite
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (d : FiniteAdelicGL F n) :
    determinantOperatorConjugation n χ hχ (finiteOperator F n d) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) • finiteOperator F n d := by
  apply Subtype.ext
  exact finiteSmoothDeterminantConjugation_finite n χ hχ d

@[simp]
theorem determinantOperatorConjugation_compact
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (k : standardInfiniteCompact F n) :
    determinantOperatorConjugation n χ hχ (compactOperator F n k) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) • compactOperator F n k := by
  apply Subtype.ext
  exact finiteSmoothDeterminantConjugation_compact n χ hχ k

@[simp]
theorem determinantOperatorConjugation_differential
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    determinantOperatorConjugation n χ hχ (differentialOperator F n a) =
      differentialOperator F n a := by
  apply Subtype.ext
  exact finiteSmoothDeterminantConjugation_differential n χ hχ a

theorem determinantOperatorConjugation_inv
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantOperatorConjugation n χ⁻¹ hχ.inv =
      (determinantOperatorConjugation n χ hχ).symm := by
  apply AlgEquiv.ext
  intro a
  rfl

/-- The actual whole-algebra covariance identity used to descend to invariant cores. -/
theorem operatorAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (a : automorphicOperatorAlgebra F n) (f : FiniteSmoothRationalFunctions F n) :
    a.val (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f) =
      FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ
        ((determinantOperatorConjugation n χ hχ a).val f) := by
  change a.val (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f) =
    FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ
      ((FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).symm
        (a.val (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f)))
  rw [ContinuousLinearEquiv.apply_symm_apply]

end Langlands.Automorphic
