/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.SmulInvertible
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

/-!
# Tensoring with the triangles `R ⟶ R ⟶ R/ϖⁿ ⟶ R⟦1⟧`

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`. This file tensors the triangles `DerivedCategory.quotPowTriangle`
with an object `Y` of `D(J, R)` and shows that `- ⊗ᴸ R/I` commutes with countable products
(`DerivedCategory.isLimit_fan_whiskerRight_quot`).

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

variable {J}

section Products

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

/-- The isomorphism `Y ≅ Y ⊗ᴸ R`, where `R` is placed in degree `0`. -/
noncomputable def unitIso (Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Y ≅ Y ⊗ (singleFunctor _ 0).obj (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))) :=
  (ρ_ Y).symm ≪≫ whiskerLeftIso Y (asIso (sheafTensorStructure J R).ε)

@[reassoc]
lemma unitIso_hom_naturality {Y Y' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (f : Y ⟶ Y') : f ≫ (unitIso Y').hom = (unitIso Y).hom ≫
      f ▷ (singleFunctor _ 0).obj (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))) := by
  simp [unitIso, whisker_exchange]

/-- Tensoring with the unit `R` placed in degree `0` commutes with products. -/
noncomputable def isLimit_fan_whiskerRight_unit
    {Y : ℕ → DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    {P : Fan Y} (hP : IsLimit P) :
    IsLimit (Fan.mk (P.pt ⊗ (singleFunctor _ 0).obj (𝟙_ (Sheaf J (ModuleCat.{u + 1} R))))
      fun j ↦ P.proj j ▷ _) :=
  Fan.IsLimit.mk _ (fun s ↦ Fan.IsLimit.lift hP (fun j ↦ s.proj j ≫ (unitIso (Y j)).inv) ≫
      (unitIso P.pt).hom)
    (fun s j ↦ by
      change (_ ≫ _) ≫ P.proj j ▷ _ = _
      simp only [assoc, ← unitIso_hom_naturality, Fan.IsLimit.fac_assoc, Iso.inv_hom_id,
        comp_id])
    (fun s m hm ↦ by
      rw [← Iso.comp_inv_eq]
      refine Fan.IsLimit.hom_ext hP _ _ fun j ↦ ?_
      rw [Fan.IsLimit.fac, ← cancel_mono (unitIso (Y j)).hom]
      simp only [assoc, unitIso_hom_naturality, Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]
      exact hm j)

/-- The triangle `Y ⊗ᴸ R ⟶ Y ⊗ᴸ R ⟶ Y ⊗ᴸ R/Iⁿ ⟶ (Y ⊗ᴸ R)⟦1⟧`. -/
noncomputable abbrev tensorQuotPowTriangle
    (Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    Triangle (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  ((curriedTensor _).obj Y).mapTriangle.obj (quotPowTriangle J hϖ hI n)

lemma tensorQuotPowTriangle_distinguished (Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    (n : ℕ) : tensorQuotPowTriangle hϖ hI Y n ∈ distTriang _ :=
  ((curriedTensor _).obj Y).map_distinguished _ (quotPowTriangle_distinguished J hϖ hI n)

/-- The morphism of triangles `tensorQuotPowTriangle Y n ⟶ tensorQuotPowTriangle Y' n` induced
by a map `Y ⟶ Y'`. -/
noncomputable def tensorQuotPowTriangleMap
    {Y Y' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (f : Y ⟶ Y') (n : ℕ) :
    tensorQuotPowTriangle hϖ hI Y n ⟶ tensorQuotPowTriangle hϖ hI Y' n where
  hom₁ := f ▷ (quotPowTriangle J hϖ hI n).obj₁
  hom₂ := f ▷ (quotPowTriangle J hϖ hI n).obj₂
  hom₃ := f ▷ (quotPowTriangle J hϖ hI n).obj₃
  comm₁ := whisker_exchange _ _
  comm₂ := whisker_exchange _ _
  comm₃ := by
    have h := NatTrans.shift_app_comm ((curriedTensor (DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} R)))).map f) (1 : ℤ) (quotPowTriangle J hϖ hI n).obj₁
    simp only [curriedTensor_map_app] at h
    change (Y ◁ (quotPowTriangle J hϖ hI n).mor₃ ≫ (Functor.commShiftIso ((curriedTensor
      (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj Y) (1 : ℤ)).hom.app
        (quotPowTriangle J hϖ hI n).obj₁) ≫ (f ▷ (quotPowTriangle J hϖ hI n).obj₁)⟦(1 : ℤ)⟧' =
      f ▷ (quotPowTriangle J hϖ hI n).obj₃ ≫ Y' ◁ (quotPowTriangle J hϖ hI n).mor₃ ≫
        (Functor.commShiftIso ((curriedTensor (DerivedCategory
          (Sheaf J (ModuleCat.{u + 1} R)))).obj Y') (1 : ℤ)).hom.app
            (quotPowTriangle J hϖ hI n).obj₁
    rw [assoc, h, whisker_exchange_assoc]

/-- The transition morphism `Y ⊗ᴸ quotPowTriangle (n + 1) ⟶ Y ⊗ᴸ quotPowTriangle n`. -/
noncomputable def tensorQuotPowTriangleTransition
    (Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    tensorQuotPowTriangle hϖ hI Y (n + 1) ⟶ tensorQuotPowTriangle hϖ hI Y n :=
  ((curriedTensor _).obj Y).mapTriangle.map (quotPowTriangleMap J hϖ hI n)

/-- Tensoring with `R/I` commutes with countable products. -/
noncomputable def isLimit_fan_whiskerRight_quot
    {Y : ℕ → DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} {P : Fan Y} (hP : IsLimit P) :
    IsLimit (Fan.mk (P.pt ⊗ (quotPowFunctor J I).obj (op 1)) fun j ↦ P.proj j ▷ _) := by
  let T := fun j ↦ tensorQuotPowTriangle hϖ hI (Y j) 1
  let ψ : tensorQuotPowTriangle hϖ hI P.pt 1 ⟶ productTriangle T :=
    productTriangle.lift T fun j ↦ tensorQuotPowTriangleMap hϖ hI (P.proj j) 1
  have hU := isLimit_fan_whiskerRight_unit (J := J) hP
  have h₁ : IsIso ψ.hom₁ := by
    have : ψ.hom₁ = (hU.conePointUniqueUpToIso (productIsProduct _)).hom := by
      refine Pi.hom_ext _ _ fun j ↦ ?_
      erw [IsLimit.conePointUniqueUpToIso_hom_comp hU (productIsProduct _) ⟨j⟩]
      simp [ψ, tensorQuotPowTriangleMap]
      rfl
    rw [this]
    infer_instance
  have h₂ : IsIso ψ.hom₂ := by
    have : ψ.hom₂ = (hU.conePointUniqueUpToIso (productIsProduct _)).hom := by
      refine Pi.hom_ext _ _ fun j ↦ ?_
      erw [IsLimit.conePointUniqueUpToIso_hom_comp hU (productIsProduct _) ⟨j⟩]
      simp [ψ, tensorQuotPowTriangleMap]
      rfl
    rw [this]
    infer_instance
  have h₃ : IsIso ψ.hom₃ := isIso₃_of_isIso₁₂ ψ (tensorQuotPowTriangle_distinguished hϖ hI _ 1)
    (productTriangle_distinguished T fun j ↦ tensorQuotPowTriangle_distinguished hϖ hI _ 1) h₁ h₂
  refine IsLimit.ofIsoLimit (productIsProduct _) (Fan.ext (asIso ψ.hom₃).symm fun j ↦ ?_)
  rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
  simp only [ψ, productTriangle.lift_hom₃, tensorQuotPowTriangleMap, Fan.mk_pt]
  exact Pi.lift_comp_π _ _

end Products

section Lemmas

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

lemma derivedCompletionCone_π_app (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    (n : ℕ) : (derivedCompletionCone J I K).π.app (op n) =
      (unitIso K).hom ≫ (tensorQuotPowTriangle hϖ hI K n).mor₂ := by
  change (ρ_ K).inv ≫ K ◁ ((sheafTensorStructure J R).ε ≫
      (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
        ((constantSheaf J (ModuleCat.{u + 1} R)).map ((Ideal.quotPowCone I).π.app (op n)))) =
    ((ρ_ K).inv ≫ K ◁ (sheafTensorStructure J R).ε) ≫
      K ◁ (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
        ((constantSheaf J (ModuleCat.{u + 1} R)).map ((Ideal.quotPowCone I).π.app (op n)))
  rw [MonoidalCategory.whiskerLeft_comp, assoc]

include hI in
lemma smul_id_tensor_quot (Z : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ϖ • 𝟙 (Z ⊗ (quotPowFunctor J I).obj (op 1)) = 0 := by
  have := smul_id_quotPowFunctor_obj J (mem_of_eq_span hI) 1
  rw [pow_one] at this
  rw [← MonoidalCategory.whiskerLeft_id, ← MonoidalLinear.whiskerLeft_smul, this,
    MonoidalPreadditive.whiskerLeft_zero]

include hI in
lemma tensor_whisker_smul_eq_zero (K Z : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    (n : ℕ) : (K ◁ ((ϖ ^ (n + 1)) • 𝟙 Z)) ▷ (quotPowFunctor J I).obj (op 1) = 0 := by
  rw [MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id,
    MonoidalLinear.smul_whiskerRight, MonoidalCategory.id_whiskerRight, pow_succ, mul_smul,
    smul_id_tensor_quot hI, smul_zero]

end Lemmas

end DerivedCategory
