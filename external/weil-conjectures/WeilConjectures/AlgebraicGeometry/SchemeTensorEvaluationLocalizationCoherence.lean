/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeTensorUnitAction

/-! # Localizing tensor evaluation against the unit
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-scheme-tensor-evaluation-localization-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_unit_comparison {C : Type*} [Category* C] [Abelian C]
    [IsGrothendieckAbelian.{u} C] [HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C]
    [Functor.HasDerivedMonoidalCategory (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (.up ℤ))] :
    let O := (HomologicalComplex.single C (.up ℤ) 0).obj (𝟙_ C)
    ((DerivedCategory.quotientCompQhIso C).app O).inv ≫
      Functor.LaxMonoidal.ε (DerivedCategory.Q (C := C)) = 𝟙 _ := by
  dsimp only
  change ((DerivedCategory.quotientCompQhIso C).app _).inv ≫
    ((𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫
      ((DerivedCategory.quotientCompQhIso C).app _).hom) = 𝟙 _
  rw [DerivedCategory.Qh.map_id]
  erw [Category.id_comp, Category.id_comp]
  exact ((DerivedCategory.quotientCompQhIso C).app _).inv_hom_id

private theorem lax_tensor_evaluation {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (L : C ⥤ D) [L.LaxMonoidal]
    (A B E : C) (e : B ⊗ E ⟶ 𝟙_ C)
    (z : L.obj (𝟙_ C) ⟶ 𝟙_ D)
    (hz : z ≫ Functor.LaxMonoidal.ε L = 𝟙 _) :
    Functor.LaxMonoidal.μ L A B ▷ L.obj E ≫
        Functor.LaxMonoidal.μ L (A ⊗ B) E ≫
        L.map ((α_ A B E).hom ≫ A ◁ e ≫ (ρ_ A).hom) =
      (α_ (L.obj A) (L.obj B) (L.obj E)).hom ≫
        L.obj A ◁ (Functor.LaxMonoidal.μ L B E ≫ L.map e ≫ z) ≫
        (ρ_ (L.obj A)).hom := by
  simp only [Functor.map_comp]
  rw [Functor.LaxMonoidal.associativity_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [Functor.LaxMonoidal.right_unitality L]
  have hzz : L.obj A ◁ z ≫ L.obj A ◁ Functor.LaxMonoidal.ε L = 𝟙 _ := by
    rw [← whiskerLeft_comp, hz, whiskerLeft_id]
  simp only [whiskerLeft_comp, Category.assoc, reassoc_of% hzz]

-- Elaborating total tensor associators uses the sheaf tensor and coproduct instances.
/-- Localization transports tensor evaluation against the single unit.
Source: Stacks Project, cohomology.tex, Tags 08DM and 08DQ;
ordinary evaluation localization proof step 2.
(blueprint: lem-pc-scheme-tensor-evaluation-localization-coherence).

Proof: Expand the tensor comparison as the lax monoidal structure of Q. Apply
its associativity law to F,V,P, then its naturality in the second variable to
e : Tot(V,P) to O. Its right-unit law identifies the remaining comparison
followed by Q of the complex right unitor with the derived right unitor after
tensoring the inverse unit comparison. Q is the composite of the monoidal
homotopy quotient with Qh, so this inverse unit comparison is precisely the
inverse quotientCompQhIso at the single unit O. Reassociate to obtain the
formula. This uses no invertibility of the tensor comparisons and applies to
any e, including zero, and to arbitrary unbounded F,V,P. -/
theorem schemeTensorEvaluation_localization_coherence (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (F V P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    ∀ e : pullbackTensorTotal Y V P ⟶ O,
      (pullbackTensorModelMap Y F V ▷ DerivedCategory.Q.obj P) ≫
          pullbackTensorModelMap Y (pullbackTensorTotal Y F V) P ≫
          DerivedCategory.Q.map
            (schemeTensorUnitAction Y F V P e) =
        (α_ (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj V)
          (DerivedCategory.Q.obj P)).hom ≫
        DerivedCategory.Q.obj F ◁
          (pullbackTensorModelMap Y V P ≫ DerivedCategory.Q.map e ≫
            ((DerivedCategory.quotientCompQhIso _).app O).inv) ≫
          (ρ_ (DerivedCategory.Q.obj F)).hom  := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).2.1
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  have := schemeModule_hasFunctorialFlatResolution Y
  have := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  have (A B : GradedObject ℤ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) :
      GradedObject.HasTensor A B := inferInstance
  let := HomologicalComplex.monoidalCategory
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  let := schemeDerivedTensorMonoidal Y
  dsimp only
  intro e
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let z := ((DerivedCategory.quotientCompQhIso _).app O).inv
  have hz : z ≫ Functor.LaxMonoidal.ε DerivedCategory.Q = 𝟙 _ :=
    derived_unit_comparison
  unfold schemeTensorUnitAction
  exact lax_tensor_evaluation DerivedCategory.Q F V P e z hz

end AlgebraicGeometry
