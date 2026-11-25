/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap

/-! # The regular coefficient product on a split finite cover -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ArtinSchreierTrace

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.lowerStar ProEtale.CondensedRing.upperStarComp
  ProEtale.CondensedRing.upperStarLowerStarAdjunction
  ProEtale.CondensedRing.monoidal_upperStar
  Mod.monoidal_extendScalars Functor.monoidal_mapMod

private theorem product_lift_isIso_of_postcomp
    {C : Type*} [Category C] {I : Type*} [HasProductsOfShape I C]
    {M R : C} {B : I → C} (p : ∀ i, M ⟶ B i) (e : ∀ i, B i ≅ R)
    (hp : IsIso (Pi.lift p)) :
    IsIso (Pi.lift (fun i ↦ p i ≫ (e i).hom)) := by
  have heq : Pi.lift (fun i ↦ p i ≫ (e i).hom) = Pi.lift p ≫ (Pi.mapIso e).hom := by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, Pi.mapIso_hom_π, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
  rw [heq]
  infer_instance

private theorem product_lift_isIso_of_components_eq
    {C : Type*} [Category C] {I : Type*} {M : C} {B : I → C} [HasProduct B]
    {p q : ∀ i, M ⟶ B i} (h : ∀ i, p i = q i) (hp : IsIso (Pi.lift p)) :
    IsIso (Pi.lift q) := by
  have he : p = q := funext h
  subst q
  exact hp

private theorem product_lift_isIso_of_reindex
    {C : Type*} [Category C] {I J : Type*} {M R : C}
    [HasProduct (fun _ : I ↦ R)] [HasProduct (fun _ : J ↦ R)]
    (e : I ≃ J) (p : J → (M ⟶ R)) (hp : IsIso (Pi.lift (fun i ↦ p (e i)))) :
    IsIso (Pi.lift p) := by
  let : HasProduct ((fun _ : J ↦ R) ∘ e) := by
    simpa only [Function.comp_def] using (inferInstance : HasProduct (fun _ : I ↦ R))
  have heq : Pi.lift p = Pi.lift (fun i ↦ p (e i)) ≫
      (Pi.reindex e (fun _ : J ↦ R)).hom := by
    apply Pi.hom_ext
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp only [Category.assoc, Pi.reindex_hom_π, Function.comp_def, Pi.lift_comp_π]
  rw [heq]
  infer_instance

private theorem splitProjection_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y T : Scheme.{u}}
    (π : Y ⟶ X) (x : T ⟶ X) (t : T ⟶ Y) (w : t ≫ π = x) :
    (((eqToIso (congrArg (ProEtale.CondensedRing.upperStar Λ) w)).symm ≪≫
        ProEtale.CondensedRing.upperStarComp Λ t π).hom.app
        ((ProEtale.CondensedRing.lowerStar Λ π).obj (condensedUnit Λ Y)) ≫
      (ProEtale.CondensedRing.upperStar Λ t).map
        ((ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app
          (condensedUnit Λ Y))) =
      ProEtale.CondensedRing.stalkLowerStarProj Λ w (condensedUnit Λ Y) := by
  subst x
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]
  rw [ProEtale.CondensedRing.stalkLowerStarProj_eq]
  simp only [ProEtale.CondensedRing.upperStarCongr_self,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp]

/-- The monoidal unit comparison, with its objects stated as regular modules.
Source: blueprint lemma-artin-schreier-character-sheaf, Step 2
(blueprint: lem-fd-as-split-regular-product). -/
@[irreducible]
def regularUnitIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    condensedUnit Λ X ≅
      (ProEtale.CondensedRing.upperStar Λ f).obj (condensedUnit Λ Y) :=
  Functor.Monoidal.εIso (ProEtale.CondensedRing.upperStar Λ f)

/-- Restriction of coefficient functions to one sheet, followed by the canonical
identification of the pulled-back regular module.
Source: blueprint lemma-artin-schreier-character-sheaf, Step 2
(blueprint: lem-fd-as-split-regular-product). -/
def sheetProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y T : Scheme.{u}}
    (π : Y ⟶ X) (x : T ⟶ X) (t : T ⟶ Y) (w : t ≫ π = x) :
    (ProEtale.CondensedRing.upperStar Λ x).obj
        ((ProEtale.CondensedRing.lowerStar Λ π).obj (condensedUnit Λ Y)) ⟶
      condensedUnit Λ T :=
  ProEtale.CondensedRing.stalkLowerStarProj Λ w (condensedUnit Λ Y) ≫
    (regularUnitIso Λ t).inv

private theorem sheetProjection_product_fin_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y T : Scheme.{u}}
    (π : Y ⟶ X) (x : T ⟶ X) [WeaklyEtale x]
    (n : ℕ) (t : Fin n → (T ⟶ Y)) (w : ∀ j, t j ≫ π = x)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback π x)
      (fun j ↦ pullback.lift (t j) (𝟙 T) (by simpa using w j))))) :
    IsIso (Pi.lift (fun j : Fin n ↦ sheetProjection Λ π x (t j) (w j))) := by
  let a (j : Fin n) :
      (ProEtale.CondensedRing.upperStar Λ x).obj
        ((ProEtale.CondensedRing.lowerStar Λ π).obj (condensedUnit Λ Y)) ⟶
      (ProEtale.CondensedRing.upperStar Λ (t j)).obj (condensedUnit Λ Y) :=
    ((eqToIso (congrArg (ProEtale.CondensedRing.upperStar Λ) (w j))).symm ≪≫
      ProEtale.CondensedRing.upperStarComp Λ (t j) π).hom.app
        ((ProEtale.CondensedRing.lowerStar Λ π).obj (condensedUnit Λ Y)) ≫
      (ProEtale.CondensedRing.upperStar Λ (t j)).map
        ((ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app
          (condensedUnit Λ Y))
  have ha : IsIso (Pi.lift a) :=
    ProEtale.CondensedRing.splitProEtaleModuleProductMap_isIso Λ π x n t w hc
      (condensedUnit Λ Y)
  have hproj (j : Fin n) : a j =
      ProEtale.CondensedRing.stalkLowerStarProj Λ (w j) (condensedUnit Λ Y) :=
    splitProjection_eq Λ π x (t j) (w j)
  exact product_lift_isIso_of_components_eq
    (fun j ↦ by rw [hproj j]; rfl)
    (product_lift_isIso_of_postcomp (R := condensedUnit Λ T) a
      (fun j ↦ (regularUnitIso Λ (t j)).symm) ha)

/-- The sheet projections identify a split finite direct image of regular coefficient
modules with the product of the regular modules on the base of the split chart.
Source: blueprint lemma-artin-schreier-character-sheaf, Step 2, and the existing module product
comparison (blueprint: lem-fd-as-split-regular-product).

Proof: reindex the given finite sheets by Fin n and apply
splitProEtaleModuleProductMap_isIso. Each target is the inverse image of a regular
module; the monoidal unit isomorphism identifies it with the regular module on T.
The product of these isomorphisms and the reindexing isomorphism give the displayed
map, as is checked after every product projection. -/
theorem sheetProjection_product_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y T : Scheme.{u}}
    (π : Y ⟶ X) (x : T ⟶ X) [WeaklyEtale x]
    (J : Type v) [Finite J] (t : J → (T ⟶ Y)) (w : ∀ j, t j ≫ π = x)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback π x)
      (fun j ↦ pullback.lift (t j) (𝟙 T) (by simpa using w j))))) :
    IsIso (Pi.lift (fun j : J ↦ sheetProjection Λ π x (t j) (w j))) := by
  classical
  let := Fintype.ofFinite J
  let e := (Fintype.equivFin J).symm
  let t' (j : Fin (Fintype.card J)) := t (e j)
  let w' (j : Fin (Fintype.card J)) := w (e j)
  have hc' : Nonempty (IsColimit (Cofan.mk (pullback π x)
      (fun j ↦ pullback.lift (t' j) (𝟙 T) (by simpa using w' j)))) :=
    ⟨(Cofan.isColimitEquivOfEquiv e _ ) hc.some⟩
  have hi := sheetProjection_product_fin_isIso Λ π x (Fintype.card J) t' w' hc'
  exact product_lift_isIso_of_reindex e
    (fun j ↦ sheetProjection Λ π x (t j) (w j)) hi

end AlgebraicGeometry.ArtinSchreierTrace
