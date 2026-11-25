/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- The termwise tilde functor in the preceding construction is compatible
with the canonical integer shift and is triangulated. This is the final
compatibility step of Stacks Project, Tag 06Z0.
Proof: Exact termwise tilde commutes with translation of complexes, including
the signed differentials, and with mapping cones. Its localization therefore
carries distinguished cone triangles to distinguished triangles and has a
compatible integer-shift structure. Transfer that structure through the
given natural isomorphism after Q. The localization universal property
descends the shift isomorphisms and their coherence to F followed by the
full-subcategory inclusion; it also descends preservation of triangles.
(blueprint: new-affine-qcoh-derived-tilde-triangulated) -/
theorem affineQCohDerivedEquivalence_core_triangulated (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
    (h : Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q)) :
    ∃ (_h : (F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).CommShift ℤ),
      (F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).IsTriangulated := by
  classical
  let T : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) :=
    tilde.functor (.of A)
  have : T.Additive := by
    constructor
    intro X Y f g
    exact tilde.map_add (R := .of A) f g
  let G := F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι
  let H := T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  obtain ⟨e⟩ := h
  let ec : HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⋙ G ≅
      HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ) ⋙ H :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)) G ≪≫
      e ≪≫
      Functor.isoWhiskerLeft _
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  let eh : DerivedCategory.Qh ⋙ G ≅ H :=
    ((Functor.whiskeringLeft _ _ _).obj
      (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ))).preimageIso ec
  let : Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) H G := ⟨eh⟩
  let := Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) ℤ H G
  refine ⟨inferInstance, ?_⟩
  have : (T.mapHomotopyCategory (ComplexShape.up ℤ)).IsTriangulated := inferInstance
  have : (DerivedCategory.Qh (C :=
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))).IsTriangulated :=
    inferInstance
  have : H.IsTriangulated := by
    dsimp [H]
    exact Functor.IsTriangulated.instComp
      (T.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh
  have : NatTrans.CommShift eh.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (Localization.Lifting.iso DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) H G).hom ℤ)
  exact Functor.isTriangulated_of_precomp_iso eh

end AlgebraicGeometry
