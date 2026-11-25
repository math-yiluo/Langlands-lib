/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitCounit
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Normalization of the explicit derived pullback unit comparison -/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local instance]
  tensorDescentPullbackDescentModuleTensor
  tensorDescentModuleSymmetric
  tensorDescentModulePreadditive
  tensorDescentModuleClosed
  tensorDescentModuleGrothendieck
  tensorDescentModuleResolutions
  tensorDescentModuleDerivedMonoidal
  tensorDescentPullbackDescentQLax

private theorem localization_unit_eq
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))] :
    Functor.LaxMonoidal.ε (DerivedCategory.Q (C := C)) =
      Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := C)) := by
  change ((Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := C)) ≫
    (DerivedCategory.Qh (C := C)).map (𝟙 _)) ≫ 𝟙 _) = _
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]

private theorem inverse_unit_comparison
    {C : Type*} {D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {a b : C} {c d e : D} (eX : a ≅ b) (eT : c ≅ d) (eF : d ≅ e)
    (ε : L.obj b ⟶ e) [IsIso ε] :
    (eT ≪≫ eF ≪≫ (asIso ε).symm ≪≫ L.mapIso eX.symm).inv ≫ eT.hom =
      L.map eX.hom ≫ ε ≫ eF.inv := by
  simp [Category.assoc]

-- The unfolding of `derivedPullback_tensorUnitIso` against the lax unit of `Q` goes through
-- the derived monoidal structure; it needs slightly more than the default budget.
/-- Normalize the explicitly constructed unit comparison before any tensor comparison is used.
Source: Stacks Project, Cohomology, Tag 079U, parent unit proof, step 1;
the explicit construction in `derivedPullback_tensorUnitIso`.
(blueprint: lem-pc-derived-pullback-tensor-unit-normalization).
Proof: Q is the homotopy quotient followed by Qh, transported along quotientCompQhIso.
The quotient unit comparison and this transport have identity components, hence
its lax unit morphism is the lax unit morphism of Qh. The latter is invertible by
DerivedCategory.isIso_ε_Qh, proving the first assertion. Write u for the single-image
unit comparison of F on complexes. The definition of tensorPullback_unitHomotopyIso
is the quotient image of u followed by the inverse functor-factorization comparison.
The latter has identity components, so Qh of its inverse is Q of u inverse.
Invert the four factors defining derivedPullback_tensorUnitIso: the result is
L of the source localization unit, then the supplied counit at U, then Q of u inverse,
then the inverse target localization unit. Compose with the target localization
unit and cancel its inverse. This proves the displayed formula. This calculation
uses no tensorator of L and no K-flatness or boundedness hypothesis. It applies
also to zero complexes, zero rings, and empty schemes. -/
theorem derivedPullback_tensorUnitIso_normalization {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace)) [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [IsIso (ε.app (𝟙_ (HomotopyCategory
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))))] :
    IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q
      (C := SheafOfModules.{uModel} (moduleRings T.toRingedSpace)))) ∧
    (let AX := SheafOfModules.{uModel} (moduleRings X.toRingedSpace)
     let AT := SheafOfModules.{uModel} (moduleRings T.toRingedSpace)
     let U : CochainComplex AX ℤ := 𝟙_ _
     let u := (HomologicalComplex.single AT (ComplexShape.up ℤ) 0).mapIso mF.εIso ≪≫
       ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app _).symm
     (derivedPullback_tensorUnitIso g F mF ε).inv ≫
         Functor.LaxMonoidal.ε (DerivedCategory.Q (C := AT)) =
       (derivedPullback g).map (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := AX))) ≫
         cast (by rfl) (ε.app ((HomotopyCategory.quotient AX (ComplexShape.up ℤ)).obj U)) ≫
           (DerivedCategory.Q (C := AT)).map u.inv) := by
  let AX := SheafOfModules.{uModel} (moduleRings X.toRingedSpace)
  let AT := SheafOfModules.{uModel} (moduleRings T.toRingedSpace)
  have hX := localization_unit_eq AX
  have hT := localization_unit_eq AT
  have := DerivedCategory.isIso_ε_Qh AX
  have := DerivedCategory.isIso_ε_Qh AT
  constructor
  · rw [hT]
    exact DerivedCategory.isIso_ε_Qh AT
  · dsimp only
    rw [hX, hT]
    have h := inverse_unit_comparison (derivedPullback g)
      (asIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := AX))))
      (asIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := AT))))
      ((DerivedCategory.Qh (C := AT)).mapIso (tensorPullback_unitHomotopyIso F mF))
      (ε.app (𝟙_ (HomotopyCategory AX (ComplexShape.up ℤ))))
    change (derivedPullback_tensorUnitIso g F mF ε).inv ≫
      Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := AT)) = _ at h
    rw [h]
    simp only [asIso_hom, CategoryTheory.Functor.mapIso_inv]
    congr 2

end AlgebraicGeometry
