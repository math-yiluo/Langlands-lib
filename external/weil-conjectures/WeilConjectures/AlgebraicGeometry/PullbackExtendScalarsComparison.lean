/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Pullback commutes with extension of scalars

The comparison follows from uniqueness of left adjoints to the naturally isomorphic
restriction-of-scalars functors. It is defined before bounded derived categories.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

omit [IsCommMonObj S] in
/-- The canonical comparison, given by uniqueness of the two left adjoints.
Source: the monoidal inverse-image adjunction and restriction of scalars.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def pullbackExtendScalarsComparison :
    Mod.extendScalars φ ⋙ (upperStar Ab.{u + 1} g).mapMod S ≅
      (upperStar Ab.{u + 1} g).mapMod R ⋙
        Mod.extendScalars ((upperStar Ab.{u + 1} g).map φ) := by
  let F := upperStar Ab.{u + 1} g
  let G := lowerStar Ab.{u + 1} g
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} g
  let a := (Mod.extendRestrictAdjunction φ).comp (adj.mapModAdjunction S)
  let b := (adj.mapModAdjunction R).comp
    (Mod.extendRestrictAdjunction (F.map φ))
  have : IsMonHom (adj.unitAlgHom R) := Adjunction.isMonHom_unitAlgHom adj R
  have : IsMonHom (adj.unitAlgHom S) := Adjunction.isMonHom_unitAlgHom adj S
  have hφ : adj.unitAlgHom R ≫ G.map (F.map φ) = φ ≫ adj.unitAlgHom S :=
    (adj.unit.naturality φ).symm
  have e : Mod.comap (F.map φ) ⋙
      (G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)) ≅
      (G.mapMod (F.obj S) ⋙ Mod.comap (adj.unitAlgHom S)) ⋙ Mod.comap φ :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapModComapIso (F.map φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapCongr hφ) ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _) ≪≫
    (Functor.associator _ _ _).symm
  exact a.leftAdjointUniq (b.ofNatIsoRight e)

end AlgebraicGeometry.ProEtale
