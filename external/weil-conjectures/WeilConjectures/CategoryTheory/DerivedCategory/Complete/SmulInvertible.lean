/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Objects on which an element acts invertibly

Let `(C, J)` be an essentially small site and `R` a commutative ring. This file defines the
class `DerivedCategory.smulInvertible J ϖ` of objects of `D(J, R)` on which `ϖ ∈ R` acts
invertibly, and shows that a derived complete object for an ideal containing `ϖ` receives no
nonzero map from such an object (`DerivedCategory.rightOrthogonal_of_derivedComplete`).

## Implementation notes

The monoidal structure of `D(J, R)` is taken from the fields of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.

-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

local instance : IsIso (sheafTensorStructure J R).ε := (sheafTensorStructure J R).isIso_ε

/-- The objects of `D(J, R)` on which `ϖ` acts invertibly. -/
def smulInvertible (ϖ : R) : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  fun X ↦ IsIso (ϖ • 𝟙 X)

variable {J}

instance (ϖ : R) (a : ℤ) : (smulInvertible J ϖ).IsStableUnderShiftBy a where
  le_shift X (hX : IsIso (ϖ • 𝟙 X)) := by
    change IsIso (ϖ • 𝟙 (X⟦a⟧))
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance

instance (ϖ : R) : (smulInvertible J ϖ).IsStableUnderShift ℤ where

lemma smulInvertible.pow {ϖ : R} {X : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hX : smulInvertible J ϖ X) (n : ℕ) : IsIso (ϖ ^ n • 𝟙 X) := by
  induction n with
  | zero => simp only [pow_zero, one_smul]; infer_instance
  | succ n ih =>
    have h₁ : IsIso (ϖ • 𝟙 X) := hX
    have e : ϖ ^ (n + 1) • 𝟙 X = (ϖ ^ n • 𝟙 X) ≫ (ϖ • 𝟙 X) := by
      rw [Linear.smul_comp, id_comp, smul_smul, pow_succ]
    rw [e]
    exact IsIso.comp_isIso' ih h₁

/-- There is no nonzero map from an object on which `ϖ` acts invertibly to an object killed by
`ϖⁿ`. -/
lemma smulInvertible.hom_eq_zero {ϖ : R} {X Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hX : smulInvertible J ϖ X) {n : ℕ} (hY : ϖ ^ n • 𝟙 Y = 0) (f : X ⟶ Y) : f = 0 := by
  have := hX.pow n
  rw [← cancel_epi (ϖ ^ n • 𝟙 X), comp_zero, Linear.smul_comp, id_comp, ← comp_id f,
    ← Linear.comp_smul, hY, comp_zero]

variable (J) in
/-- `ϖⁿ` acts by zero on `R/Iⁿ`, placed in degree `0` of `D(J, R)`, when `ϖ ∈ I`. -/
lemma smul_id_quotPowFunctor_obj {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ I) (n : ℕ) :
    ϖ ^ n • 𝟙 ((quotPowFunctor J I).obj (op n)) = 0 := by
  change ϖ ^ n • 𝟙 ((singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).obj
    ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R (R ⧸ I ^ n)))) = 0
  have h : ϖ ^ n • 𝟙 (ModuleCat.of R (R ⧸ I ^ n)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖ n)
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_id, ← Functor.map_smul,
    ← Functor.map_smul, h, Functor.map_zero, Functor.map_zero]

variable (J) in
/-- `ϖⁿ` acts by zero on the reduction `K ⊗ᴸ R/Iⁿ` when `ϖ ∈ I`. -/
lemma smul_id_derivedCompletionDiagram_obj {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ I)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    ϖ ^ n • 𝟙 ((derivedCompletionDiagram J I K).obj (op n)) = 0 := by
  change ϖ ^ n • 𝟙 (K ⊗ (quotPowFunctor J I).obj (op n)) = 0
  rw [← MonoidalCategory.whiskerLeft_id, ← MonoidalLinear.whiskerLeft_smul,
    smul_id_quotPowFunctor_obj J hϖ n, MonoidalPreadditive.whiskerLeft_zero]

/-- A derived complete object receives no nonzero map from an object on which `ϖ` acts
invertibly, when `ϖ ∈ I`. -/
lemma rightOrthogonal_of_derivedComplete {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ I)
    {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (hK : derivedComplete J I K) :
    (smulInvertible J ϖ).rightOrthogonal K := fun X f hX ↦
  IsHomotopyLimit.hom_ext_zero hK
    (fun n g ↦ hX.hom_eq_zero (smul_id_derivedCompletionDiagram_obj J hϖ K n) g)
    (fun n g ↦ (ObjectProperty.le_shift _ 1 X hX).hom_eq_zero
      (smul_id_derivedCompletionDiagram_obj J hϖ K n) g) f

end DerivedCategory
