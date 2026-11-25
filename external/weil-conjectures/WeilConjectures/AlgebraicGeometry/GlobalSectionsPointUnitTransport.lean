/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

@[expose] public section

universe u w wA wPt
open CategoryTheory Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

-- The point map has identity scalar map on global sections.
private noncomputable def point_sections_comparison (Y : Scheme.{u}) :
    RingedSpace.moduleDirectImage (toGlobalSectionsPoint Y) ⋙
      RingedSpace.globalSectionsFunctor (globalSectionsPoint Y) ≅
      RingedSpace.globalSectionsFunctor Y.toRingedSpace := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · change (ModuleCat.restrictScalars (RingHom.id _)).obj (M.val.obj (op ⊤)) ≅
      M.val.obj (op ⊤)
    exact (ModuleCat.restrictScalarsId _).app _
  · intro M N g
    apply ModuleCat.hom_ext
    rfl

-- Exact postcomposition transports an invertible unit by right-derived uniqueness.
private theorem unit_isIso_comp_of_exact
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (J : HomotopyCategory C (ComplexShape.up ℤ))
    [IsIso (F.rightDerivedFunctorUnit.app J)] :
    IsIso ((F ⋙ G).rightDerivedFunctorUnit.app J) := by
  let β := Functor.rightDerivedFunctorCompUnit F G
  have := Functor.isRightDerivedFunctor_rightDerivedFunctor_comp_of_exact F G
  let δ := (F ⋙ G).rightDerivedFunctor.rightDerivedDesc
    (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) β
  have : IsIso δ :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (F ⋙ G).rightDerivedFunctor
      (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) β).mp inferInstance
  have hβ : IsIso (β.app J) := by
    dsimp [β, Functor.rightDerivedFunctorCompUnit]
    infer_instance
  have h : (F ⋙ G).rightDerivedFunctorUnit.app J ≫ δ.app (DerivedCategory.Qh.obj J) =
      β.app J := Functor.rightDerived_fac_app _ _ _ _ _ _
  have : IsIso ((F ⋙ G).rightDerivedFunctorUnit.app J ≫
      δ.app (DerivedCategory.Qh.obj J)) := by rw [h]; exact hβ
  exact IsIso.of_isIso_comp_right ((F ⋙ G).rightDerivedFunctorUnit.app J)
    (δ.app (DerivedCategory.Qh.obj J))

-- The derived natural isomorphism commutes with the two units.
private theorem unit_isIso_of_natIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (J : HomotopyCategory C (ComplexShape.up ℤ))
    [IsIso (F.rightDerivedFunctorUnit.app J)] :
    IsIso (G.rightDerivedFunctorUnit.app J) := by
  let ε : F.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      G.mapHomotopyCategory (ComplexShape.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)
      inv := NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id]
        exact NatTrans.mapHomotopyCategory_id _ _
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id]
        exact NatTrans.mapHomotopyCategory_id _ _ }
  let δ := Functor.rightDerivedFunctorNatIso e
  let τ := Functor.whiskerRight
    (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)) DerivedCategory.Qh
  have : IsIso τ := inferInstanceAs (IsIso (Functor.isoWhiskerRight ε DerivedCategory.Qh).hom)
  have h : F.rightDerivedFunctorUnit.app J ≫ δ.hom.app (DerivedCategory.Qh.obj J) =
      τ.app J ≫ G.rightDerivedFunctorUnit.app J :=
    Functor.rightDerivedNatTrans_app F.rightDerivedFunctor G.rightDerivedFunctor
      F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) τ J
  have : IsIso (τ.app J ≫ G.rightDerivedFunctorUnit.app J) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (τ.app J) (G.rightDerivedFunctorUnit.app J)

/-- Transport of the direct-image unit along the global-sections point comparison.
Source: Stacks Project, Cohomology, Tags 079W and 0D5T; Duality, Tag 0B6I.
(blueprint: new-global-sections-point-unit-transport).

The equivalence between module sheaves on the global-sections point and modules over
its global ring identifies direct image along the point map with global sections.
The comparison of right-derived functors is compatible with the units.  Conjugating
the invertible point unit by these comparison isomorphisms therefore gives an
invertible global-sections unit.  This is the categorical transport step in the
proof of global-sections acyclicity.
-/
theorem globalSections_unit_isIso_of_point_unit
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))]
    [HasDerivedCategory.{wPt}
      (SheafOfModules.{u} (moduleRings (globalSectionsPoint Y)))]
    (f : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (h : IsIso
      ((RingedSpace.moduleDirectImage (toGlobalSectionsPoint Y)).rightDerivedFunctorUnit.app
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)))) :
    IsIso ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
  let F := RingedSpace.moduleDirectImage (toGlobalSectionsPoint Y)
  let G : SheafOfModules.{u} (moduleRings (globalSectionsPoint Y)) ⥤
      ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)) :=
    RingedSpace.globalSectionsFunctor (globalSectionsPoint Y)
  let J := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
    (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)
  obtain ⟨e, ⟨he⟩, _⟩ := schemeDerivedGlobalSections_point_comparison Y
  let : CategoryTheory.Limits.PreservesFiniteLimits G :=
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso he
  let : CategoryTheory.Limits.PreservesFiniteColimits G :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso he
  let : IsIso (F.rightDerivedFunctorUnit.app J) := h
  let : IsIso ((F ⋙ G).rightDerivedFunctorUnit.app J) :=
    unit_isIso_comp_of_exact F G J
  exact unit_isIso_of_natIso (F := F ⋙ G)
    (G := RingedSpace.globalSectionsFunctor Y.toRingedSpace) (point_sections_comparison Y) J

end AlgebraicGeometry
