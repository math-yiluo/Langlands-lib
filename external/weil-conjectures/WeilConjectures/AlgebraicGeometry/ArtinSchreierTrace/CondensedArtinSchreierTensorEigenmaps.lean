/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierIsotypicRecognition
import Mathlib.Tactic.Ring
import WeilConjectures.AlgebraicGeometry.AffineSpace.FiniteFieldArtinSchreierMap
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierScalars
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierProjectorFacts
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj

/-! # Eigenmaps on the product Artin--Schreier torsor

Source: blueprint lemma-artin-schreier-character-sheaf, proof Step 5, root addition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
open AlgebraicGeometry ProEtale ProEtale.CondensedRing
namespace AlgebraicGeometry.ArtinSchreierTrace

/-- The character of the product torsor, (a,b) ↦ ψ(a)ψ(b).
Source: blueprint lemma-artin-schreier-character-sheaf Step 5
(blueprint: lem-fd-as-tensor-eigenmaps). -/
def tensorAddCharacter {k R : Type*} [AddCommGroup k] [CommMonoid R]
    (ψ : AddChar k R) : AddChar (k × k) R :=
  ψ.compAddMonoidHom (AddMonoidHom.fst k k) *
    ψ.compAddMonoidHom (AddMonoidHom.snd k k)

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.upperStarComp ProEtale.CondensedRing.lowerStarComp
  ProEtale.CondensedRing.upperStarLowerStarAdjunction
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
private abbrev reg (X : Scheme.{u}) := Mod.regular (condensedRingObj Λ X)
/- Regular-section pullback and its functoriality over varying covers. -/
private def unitPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    reg Λ Y ⟶ (CondensedRing.lowerStar Λ f).obj (reg Λ X) :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv

private theorem unitPush_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (unitPush Λ f).hom = condensedPushforwardHom Λ f :=
  CondensedRing.homEquiv_εIso_inv_hom Λ f

private theorem unitPush_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    unitPush Λ (f ≫ g) = unitPush Λ g ≫
      (CondensedRing.lowerStar Λ g).map (unitPush Λ f) ≫
        (CondensedRing.lowerStarComp Λ f g).hom.app (reg Λ X) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', lowerStar_map_hom,
    lowerStarComp_hom_app_hom, unitPush_hom]
  exact condensedPushforwardHom_comp Λ f g

private def mapOver {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    (t : Z ⟶ Y) (h : t ≫ f = g) :
    (CondensedRing.lowerStar Λ f).obj (reg Λ Y) ⟶
      (CondensedRing.lowerStar Λ g).obj (reg Λ Z) :=
  (CondensedRing.lowerStar Λ f).map (unitPush Λ t) ≫
    (CondensedRing.lowerStarComp Λ t f).hom.app (reg Λ Z) ≫
      (CondensedRing.lowerStarCongr Λ h).hom.app (reg Λ Z)

omit [IsCommMonObj Λ] in
private theorem lowerStarCongr_app {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    (CondensedRing.lowerStarCongr Λ h).hom.app (reg Λ Y) =
      eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar Λ t).obj (reg Λ Y)) h) := by
  cases h
  rfl

private theorem mapOver_congr {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    {t s : Z ⟶ Y} (h : t = s) (ht : t ≫ f = g) (hs : s ≫ f = g) :
    mapOver Λ f g t ht = mapOver Λ f g s hs := by
  subst s
  rfl

private theorem mapOver_comp {X Y Z W : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ X) (j : W ⟶ X)
    (t : Z ⟶ Y) (s : W ⟶ Z) (h : t ≫ f = g) (hs : s ≫ g = j) :
    mapOver Λ f j (s ≫ t) (by rw [Category.assoc, h, hs]) =
      mapOver Λ f g t h ≫ mapOver Λ g j s hs := by
  subst g
  subst j
  unfold mapOver
  rw [unitPush_comp]
  simp only [Functor.map_comp, Category.assoc]
  have hc := congrArg (fun e ↦ e.hom.app (reg Λ W))
    (lowerStarComp_assoc Λ s t f)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Category.id_comp, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hc
  simp only [CondensedRing.lowerStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp] at hc ⊢
  erw [← hc]
  rw [← NatTrans.naturality_assoc]
  rfl

private theorem mapOver_push {X X' Y Z : Scheme.{u}} (n : X ⟶ X')
    (f : Y ⟶ X) (g : Z ⟶ X) (t : Z ⟶ Y) (h : t ≫ f = g) :
    (CondensedRing.lowerStar Λ n).map (mapOver Λ f g t h) ≫
        (CondensedRing.lowerStarComp Λ g n).hom.app (reg Λ Z) =
      (CondensedRing.lowerStarComp Λ f n).hom.app (reg Λ Y) ≫
        mapOver Λ (f ≫ n) (g ≫ n) t (by rw [← Category.assoc, h]) := by
  subst g
  unfold mapOver
  simp only [CondensedRing.lowerStarCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, Functor.map_comp, Category.assoc]
  have hc := congrArg (fun e ↦ e.hom.app (reg Λ Z))
    (lowerStarComp_assoc Λ t f n)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Category.id_comp, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hc
  simp only [CondensedRing.lowerStarCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] at hc
  erw [← hc, ← NatTrans.naturality_assoc]
  rfl

private abbrev modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

private theorem additiveFromPoint (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

attribute [local instance] additiveFromPoint

private def scalars (X : Scheme.{u}) : MonObj.Γ Λ →+* MonObj.Γ (condensedRingObj Λ X) :=
  MonObj.Γ.mapFunctor (upperStarFromPoint X)

@[instance_reducible] private def linearModules (X : Scheme.{u}) :
    Linear (MonObj.Γ Λ) (modules Λ X) := Mod.linearOfRingHom (scalars Λ X)

attribute [local instance] linearModules

private theorem linearLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).Linear (MonObj.Γ Λ) := by
  unfold CondensedRing.lowerStar
  apply Mod.linear_mapMod_comp_comap
    (ProEtale.lowerStar Ab.{u + 1} f) (condensedPushforwardHom _ f)
    (scalars Λ X) (scalars Λ Y)
  intro a
  simp only [scalars, MonObj.Γ.mapFunctor_hom,
    condensedPushforwardHom, Adjunction.unitAlgHom, Category.assoc]
  exact Adjunction.ε_comp_map_comp_unit_app_comp_map
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
    (upperStarFromPoint Y) (upperStarFromPoint X) (upperStarFromPointComp f).hom a.hom

attribute [local instance] linearLowerStar

private theorem linearUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).Linear (MonObj.Γ Λ) :=
  (CondensedRing.upperStarLowerStarAdjunction _ f).left_adjoint_linear

attribute [local instance] linearUpperStar

private theorem scalarEnd (X : Scheme.{u}) (a : MonObj.Γ Λ) :
    (Mod.regularEndRingHom (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint X) a)).asHom =
      a • 𝟙 (Mod.regular (condensedRingObj Λ X)) := by
  rw [Mod.linearOfRingHom_smul_id (scalars Λ X)]
  apply Mod.hom_ext
  change (ρ_ _).inv ≫ _ ◁ (scalars Λ X a).hom ≫ MonObj.mul =
    (λ_ _).inv ≫ (scalars Λ X a).hom ▷ _ ≫ MonObj.mul
  exact Mod.rightUnitor_inv_whiskerLeft_mul_eq
    (S := condensedRingObj Λ X) (scalars Λ X a).hom


private theorem pull_eq_mapOver {X : Scheme.{u}} {Y Z : Over X} (h : Y ⟶ Z) :
    condensedPull Λ h = mapOver Λ Z.hom Y.hom h.left (Over.w h) := by
  unfold condensedPull mapOver
  congr 2
  apply Mod.regular_hom_ext
  rw [Mod.one_comp_regularLift, unitPush_hom]

/- Adjunction mates identify evaluation at a root with the sheet projection. -/
private theorem abstract_mapOver_adjoint
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    (af : F ⊣ G) (ah : H ⊣ I) (ag : L ⊣ R) (θ : L ≅ F ⋙ H)
    (M : D) (N : E) (η : H.obj M ⟶ N) :
    L.map (G.map (ah.homEquiv _ _ η) ≫
      (conjugateIsoEquiv (af.comp ah) ag θ).hom.app N) ≫ ag.counit.app N =
      θ.hom.app (G.obj M) ≫ H.map (af.counit.app M) ≫ η := by
  have h := homEquiv_comp_conjugateEquiv_app (af.comp ah) ag θ.hom
    (H.map (af.counit.app M) ≫ η)
  rw [Adjunction.comp_homEquiv] at h
  change af.homEquiv _ _ (ah.homEquiv _ _ (H.map (af.counit.app M) ≫ η)) ≫
      (conjugateEquiv (af.comp ah) ag θ.hom).app N =
    ag.homEquiv _ _ (θ.hom.app _ ≫ H.map (af.counit.app M) ≫ η) at h
  rw [ah.homEquiv_naturality_left, af.homEquiv_naturality_right] at h
  have hc : af.homEquiv _ _ (af.counit.app M) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact af.right_triangle_components M
  rw [hc, Category.id_comp] at h
  simp only [Functor.id_obj] at h
  calc
    _ = (ag.homEquiv _ _).symm
        (G.map (ah.homEquiv _ _ η) ≫
          (conjugateEquiv (af.comp ah) ag θ.hom).app N) :=
      (ag.homEquiv_counit _ _ _).symm
    _ = _ := by rw [h, Equiv.symm_apply_apply]

private theorem mapOver_adjoint {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    (t : Z ⟶ Y) (h : t ≫ f = g) :
    (CondensedRing.upperStar Λ g).map (mapOver Λ f g t h) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ g).counit.app (reg Λ Z) =
    CondensedRing.stalkLowerStarProj Λ h (reg Λ Y) ≫
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ t)).inv := by
  subst g
  have hh := abstract_mapOver_adjoint
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ t)
    (CondensedRing.upperStarLowerStarAdjunction Λ (t ≫ f))
    (CondensedRing.upperStarComp Λ t f)
    (𝟙_ (modules Λ Y)) (𝟙_ (modules Λ Z))
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ t)).inv
  rw [CondensedRing.conjugateIsoEquiv_upperStarComp] at hh
  simpa only [mapOver, unitPush, reg, CondensedRing.stalkLowerStarProj_eq,
    CondensedRing.lowerStarCongr, CondensedRing.upperStarCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp,
    Mod.tensorUnit_eq_regular, Category.assoc] using hh

private theorem abstract_composite_adjoint
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    (af : F ⊣ G) (ah : H ⊣ I) (ag : L ⊣ R) (θ : L ≅ F ⋙ H)
    (M : C) (N : E) (a : M ⟶ R.obj N) :
    ((af.comp ah).homEquiv M N).symm
      (a ≫ (conjugateIsoEquiv (af.comp ah) ag θ).inv.app N) =
      θ.inv.app M ≫ (ag.homEquiv M N).symm a := by
  let c := conjugateIsoEquiv (af.comp ah) ag θ
  have h := homEquiv_comp_conjugateEquiv_app (af.comp ah) ag θ.hom
    (θ.inv.app M ≫ (ag.homEquiv M N).symm a)
  simp only [Iso.hom_inv_id_app_assoc, Equiv.apply_symm_apply] at h
  apply ((af.comp ah).homEquiv M N).injective
  rw [Equiv.apply_symm_apply]
  apply (cancel_mono (c.hom.app N)).1
  rw [Category.assoc, c.inv_hom_id_app, Category.comp_id]
  simpa only [c, conjugateIsoEquiv_apply_hom] using h.symm

@[irreducible] private def regularPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).obj (reg Λ Y) ≅ reg Λ X :=
  (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm

private theorem sheet_evaluation {A Y : Scheme.{u}}
    (q : A ⟶ A) (r : Y ⟶ A) (w : Y ⟶ A) (hr : r ≫ q = w)
    {L : modules Λ A} (i : L ⟶ (CondensedRing.lowerStar Λ q).obj (reg Λ A)) :
    (CondensedRing.upperStar Λ w).map i ≫
      CondensedRing.stalkLowerStarProj Λ hr (reg Λ A) =
    eqToHom (congrArg (fun w : Y ⟶ A ↦ (CondensedRing.upperStar Λ w).obj L)
      hr.symm) ≫
      (CondensedRing.upperStarComp Λ r q).hom.app L ≫
        (CondensedRing.upperStar Λ r).map
          ((CondensedRing.upperStar Λ q).map i ≫
            (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app (reg Λ A)) := by
  subst w
  have hn := (CondensedRing.upperStarComp Λ r q).hom.naturality i
  simp only [Functor.comp_map] at hn
  simp only [CondensedRing.stalkLowerStarProj_eq, CondensedRing.upperStarCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp, eqToHom_refl]
  rw [reassoc_of% hn, ← Functor.map_comp]

private def rootMap {X Y A : Scheme.{u}} (π : Y ⟶ X) (v : X ⟶ A) (q : A ⟶ A)
    (r : Y ⟶ A) (h : r ≫ q = π ≫ v) {L : modules Λ A}
    (i : L ⟶ (CondensedRing.lowerStar Λ q).obj (reg Λ A)) :
    (CondensedRing.upperStar Λ v).obj L ⟶
      (CondensedRing.lowerStar Λ π).obj (reg Λ Y) :=
  (CondensedRing.upperStar Λ v).map (i ≫ mapOver Λ q (π ≫ v) r h ≫
    (CondensedRing.lowerStarComp Λ π v).inv.app (reg Λ Y)) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ v).counit.app _

private theorem rootMap_adjoint {X Y A : Scheme.{u}}
    (π : Y ⟶ X) (v : X ⟶ A) (q : A ⟶ A)
    (r : Y ⟶ A) (h : r ≫ q = π ≫ v) {L : modules Λ A}
    (i : L ⟶ (CondensedRing.lowerStar Λ q).obj (reg Λ A)) :
    (CondensedRing.upperStar Λ π).map (rootMap Λ π v q r h i) ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y) =
      (CondensedRing.upperStarComp Λ π v).inv.app L ≫
        (CondensedRing.upperStar Λ (π ≫ v)).map i ≫
        CondensedRing.stalkLowerStarProj Λ h (reg Λ A) ≫
        (regularPullIso Λ r).hom := by
  have hh := abstract_composite_adjoint
    (CondensedRing.upperStarLowerStarAdjunction Λ v)
    (CondensedRing.upperStarLowerStarAdjunction Λ π)
    (CondensedRing.upperStarLowerStarAdjunction Λ (π ≫ v))
    (CondensedRing.upperStarComp Λ π v) L (reg Λ Y)
    (i ≫ mapOver Λ q (π ≫ v) r h)
  rw [CondensedRing.conjugateIsoEquiv_upperStarComp] at hh
  simp only [Adjunction.comp_homEquiv, Equiv.symm_trans_apply] at hh
  change (CondensedRing.upperStar Λ π).map
      ((CondensedRing.upperStar Λ v).map
        ((i ≫ mapOver Λ q (π ≫ v) r h) ≫
          (CondensedRing.lowerStarComp Λ π v).inv.app (reg Λ Y)) ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ v).counit.app _) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app _ =
    (CondensedRing.upperStarComp Λ π v).inv.app L ≫
      (CondensedRing.upperStar Λ (π ≫ v)).map (i ≫ mapOver Λ q (π ≫ v) r h) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ (π ≫ v)).counit.app _ at hh
  simp only [Category.assoc] at hh
  rw [rootMap, hh]
  simp only [Functor.map_comp, Category.assoc]
  rw [mapOver_adjoint]
  unfold regularPullIso
  rfl

private theorem rootMap_comp {X Y A : Scheme.{u}}
    (π : Y ⟶ X) (v : X ⟶ A) (q : A ⟶ A)
    (r : Y ⟶ A) (h : r ≫ q = π ≫ v) {L : modules Λ A}
    (i : L ⟶ (CondensedRing.lowerStar Λ q).obj (reg Λ A))
    (τ : Y ⟶ Y) (hτ : τ ≫ π = π) (σ : A ⟶ A) (hσ : σ ≫ q = q)
    (c : MonObj.Γ Λ) (hc : τ ≫ r = r ≫ σ)
    (hi : i ≫ mapOver Λ q q σ hσ = c • i) :
    rootMap Λ π v q r h i ≫ mapOver Λ π π τ hτ =
      c • rootMap Λ π v q r h i := by
  have hn := (CondensedRing.upperStarLowerStarAdjunction Λ v).counit.naturality
    (mapOver Λ π π τ hτ)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have e₁ : (CondensedRing.lowerStarComp Λ π v).inv.app (reg Λ Y) ≫
      (CondensedRing.lowerStar Λ v).map (mapOver Λ π π τ hτ) =
    mapOver Λ (π ≫ v) (π ≫ v) τ (by rw [← Category.assoc, hτ]) ≫
      (CondensedRing.lowerStarComp Λ π v).inv.app (reg Λ Y) := by
    apply (cancel_mono ((CondensedRing.lowerStarComp Λ π v).hom.app (reg Λ Y))).1
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [mapOver_push]
    simp only [Iso.inv_hom_id_app_assoc]
  have e₂ : mapOver Λ q (π ≫ v) r h ≫
      mapOver Λ (π ≫ v) (π ≫ v) τ (by rw [← Category.assoc, hτ]) =
    mapOver Λ q q σ hσ ≫ mapOver Λ q (π ≫ v) r h := by
    rw [← mapOver_comp, ← mapOver_comp]
    exact mapOver_congr Λ _ _ hc _ _
  rw [rootMap, Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp,
    Category.assoc, Category.assoc, e₁, reassoc_of% e₂,
    ← Category.assoc i, hi, Linear.smul_comp, Functor.map_smul, Linear.smul_comp]

/- Multiplication on the direct image is compatible with deck maps and evaluation. -/
private theorem abstract_pushMul_deck
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : C ⥤ C) (G : C ⥤ D) [H.LaxMonoidal] [G.LaxMonoidal]
    (c : H ⋙ G ⟶ G) [NatTrans.IsMonoidal c] :
    let t := G.map (Functor.LaxMonoidal.ε H) ≫ c.app (𝟙_ C)
    (Functor.LaxMonoidal.μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom) ≫ t =
      (t ⊗ₘ t) ≫ Functor.LaxMonoidal.μ G (𝟙_ C) (𝟙_ C) ≫
        G.map (λ_ (𝟙_ C)).hom := by
  let t := G.map (Functor.LaxMonoidal.ε H) ≫ c.app (𝟙_ C)
  have : IsMonHom t := by dsimp only [t]; infer_instance
  exact IsMonHom.mul_hom t

attribute [local instance] CondensedRing.moduleLowerStarMonoidal

private theorem unitPush_eq_ε {X Y : Scheme.{u}} (f : X ⟶ Y) :
    unitPush Λ f = Functor.LaxMonoidal.ε (CondensedRing.lowerStar Λ f) := by
  rw [Adjunction.IsMonoidal.leftAdjoint_ε
    (adj := CondensedRing.upperStarLowerStarAdjunction Λ f)]
  rw [unitPush, Functor.Monoidal.εIso_inv, Adjunction.homEquiv_unit]
  simp only [Mod.tensorUnit_eq_regular, reg]

private def pushMul {X Y : Scheme.{u}} (π : Y ⟶ X) :
    (CondensedRing.lowerStar Λ π).obj (reg Λ Y) ⊗
        (CondensedRing.lowerStar Λ π).obj (reg Λ Y) ⟶
      (CondensedRing.lowerStar Λ π).obj (reg Λ Y) :=
  Functor.LaxMonoidal.μ (CondensedRing.lowerStar Λ π) (reg Λ Y) (reg Λ Y) ≫
    (CondensedRing.lowerStar Λ π).map (λ_ (reg Λ Y)).hom

private theorem pushMul_deck {X Y : Scheme.{u}} (π : Y ⟶ X)
    (τ : Y ⟶ Y) (hτ : τ ≫ π = π) :
    pushMul Λ π ≫ mapOver Λ π π τ hτ =
      (mapOver Λ π π τ hτ ⊗ₘ mapOver Λ π π τ hτ) ≫ pushMul Λ π := by
  let H := CondensedRing.lowerStar Λ τ
  let G := CondensedRing.lowerStar Λ π
  let c : H ⋙ G ⟶ G := (CondensedRing.lowerStarComp Λ τ π).hom ≫
    (CondensedRing.lowerStarCongr Λ hτ).hom
  have := CondensedRing.moduleLowerStarCompIsMonoidal Λ τ π
  have := CondensedRing.moduleLowerStarCongrIsMonoidal Λ hτ
  have : NatTrans.IsMonoidal c := by dsimp only [c]; infer_instance
  have hh := abstract_pushMul_deck H G c
  simpa only [mapOver, pushMul, unitPush_eq_ε, H, G, c, NatTrans.comp_app,
    Mod.tensorUnit_eq_regular, Category.assoc] using hh

private theorem tensor_adjoint_isIso {X Y : Scheme.{u}} (π : Y ⟶ X)
    {L M : modules Λ X}
    (φ : L ⟶ (CondensedRing.lowerStar Λ π).obj (reg Λ Y))
    (ψ : M ⟶ (CondensedRing.lowerStar Λ π).obj (reg Λ Y))
    [IsIso ((CondensedRing.upperStar Λ π).map φ ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y))]
    [IsIso ((CondensedRing.upperStar Λ π).map ψ ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y))] :
    IsIso ((CondensedRing.upperStar Λ π).map ((φ ⊗ₘ ψ) ≫ pushMul Λ π) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y)) := by
  have := CondensedRing.moduleAdjunctionIsMonoidal Λ π
  have hn := (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.naturality
    (λ_ (reg Λ Y)).hom
  simp only [Functor.comp_map, Functor.id_map, Mod.tensorUnit_eq_regular] at hn
  have hu : (CondensedRing.upperStar Λ π).map ((φ ⊗ₘ ψ) ≫ pushMul Λ π) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y) =
    Functor.OplaxMonoidal.δ (CondensedRing.upperStar Λ π) L M ≫
      (((CondensedRing.upperStar Λ π).map φ ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y)) ⊗ₘ
       ((CondensedRing.upperStar Λ π).map ψ ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y))) ≫
      (λ_ (reg Λ Y)).hom := by
    simp only [pushMul, Functor.map_comp, Category.assoc, hn]
    rw [Adjunction.map_μ_comp_counit_app_tensor_assoc
      (CondensedRing.upperStarLowerStarAdjunction Λ π) (reg Λ Y) (reg Λ Y)]
    rw [← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom_assoc]
  rw [hu]
  infer_instance

variable (k : Type u) [Field k] [Fintype k]

private theorem translation_mapOver (a : k) :
    (ProEtale.condensedArtinSchreierTranslationAction Λ k a).asHom =
      mapOver Λ
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))
        (Etale.artinSchreierTranslation k a)
        (Etale.artinSchreierTranslation_comp_artinSchreierMap k a) := by
  unfold ProEtale.condensedArtinSchreierTranslationAction mapOver unitPush
  rw [lowerStarCongr_app]
  rfl

private theorem translation_add (a b : k) :
    (ProEtale.condensedArtinSchreierTranslationAction Λ k a).asHom ≫
      (ProEtale.condensedArtinSchreierTranslationAction Λ k b).asHom =
        (ProEtale.condensedArtinSchreierTranslationAction Λ k (a + b)).asHom := by
  rw [translation_mapOver, translation_mapOver, translation_mapOver, ← mapOver_comp]
  apply mapOver_congr
  rw [← Etale.artinSchreierTranslation_add, add_comm]

/- Reindexing the character average gives the eigenrelation on its image. -/
private theorem sum_eigen
    {C : Type*} [Category C] [Preadditive C]
    {R : Type*} [CommRing R] [Linear R C]
    {K : Type*} [AddCommGroup K] [Fintype K]
    {P : C} (τ : K → (P ⟶ P)) (hτ : ∀ a b, τ a ≫ τ b = τ (a + b))
    (ψ : AddChar K R) (q : R) (b : K) :
    (∑ a : K, (q * ψ (-a)) • τ a) ≫ τ b =
      ψ b • (∑ a : K, (q * ψ (-a)) • τ a) := by
  classical
  simp only [Preadditive.sum_comp, Linear.smul_comp, hτ, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.addRight b) _ _ fun a ↦ ?_
  simp only [Equiv.coe_addRight, neg_add_rev]
  congr 1
  have hb : ψ b * ψ (-b) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [AddChar.map_add_eq_mul]
  symm
  calc
    _ = (q * ψ (-a)) * (ψ b * ψ (-b)) := by ring
    _ = _ := by rw [hb, mul_one]

private theorem image_eigen
    [Invertible (Fintype.card k : MonObj.Γ Λ)]
    (ψ : AddChar k (MonObj.Γ Λ)) (b : k) :
    image.ι (ProEtale.condensedArtinSchreierProjector Λ k ψ).asHom ≫
      (ProEtale.condensedArtinSchreierTranslationAction Λ k b).asHom =
        ψ b • image.ι (ProEtale.condensedArtinSchreierProjector Λ k ψ).asHom := by
  classical
  rw [← cancel_epi (factorThruImage _), image.fac_assoc, Linear.comp_smul, image.fac]
  have hp : (ProEtale.condensedArtinSchreierProjector Λ k ψ).asHom =
      ∑ a : k, (⅟(Fintype.card k : MonObj.Γ Λ) * ψ (-a)) •
        (ProEtale.condensedArtinSchreierTranslationAction Λ k a).asHom := by
    simpa only [End.sum_asHom, End.smul_asHom] using
      congrArg End.asHom (ProEtale.condensedArtinSchreierProjector_eq_sum Λ k ψ)
  simpa only [hp] using sum_eigen
    (fun a ↦ (ProEtale.condensedArtinSchreierTranslationAction Λ k a).asHom)
    (translation_add Λ k)
    ψ (⅟(Fintype.card k : MonObj.Γ Λ)) b


open Etale

local notation "𝔸₁[" K "]" => 𝔸(PUnit; Spec (CommRingCat.of K))
local notation "𝔸₂[" K "]" =>
  pullback (𝔸₁[K] ↘ Spec (CommRingCat.of K)) (𝔸₁[K] ↘ Spec (CommRingCat.of K))

/- Pull back the universal product torsor and its translation action. -/
private def universalAction : Multiplicative (k × k) →* Aut (Over.mk (artinSchreierMapProd k)) where
  toFun a := Aut.of
    { hom := Over.homMk (artinSchreierTranslationProd k a.toAdd)
      inv := Over.homMk (artinSchreierTranslationProd k (-a.toAdd))
      hom_inv_id := by
        ext
        simp only [Over.comp_left, Over.homMk_left, Over.id_left]
        rw [← artinSchreierTranslationProd_add, add_neg_cancel,
          artinSchreierTranslationProd_zero]
        rfl
      inv_hom_id := by
        ext
        simp only [Over.comp_left, Over.homMk_left, Over.id_left]
        rw [← artinSchreierTranslationProd_add, neg_add_cancel,
          artinSchreierTranslationProd_zero]
        rfl }
  map_one' := by
    ext
    exact artinSchreierTranslationProd_zero
  map_mul' a b := by
    ext
    change artinSchreierTranslationProd k (a.toAdd + b.toAdd) =
      artinSchreierTranslationProd k b.toAdd ≫ artinSchreierTranslationProd k a.toAdd
    rw [add_comm, artinSchreierTranslationProd_add]

private theorem coverGeometry (k : Type u) [Field k] [Fintype k]
    (X : Scheme.{u}) (h : X ⟶ 𝔸₂[k]) :
    ∃ Y : Over X, IsFinite Y.hom ∧ Etale Y.hom ∧
      Function.Surjective Y.hom.base ∧
      ∃ σ : Multiplicative (k × k) →* Aut Y,
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (s t : Spec (.of Ω) ⟶ Y.left), s ≫ Y.hom = t ≫ Y.hom →
            ∃ a : k × k, s = t ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left) ∧
        ∃ t : Y.left ⟶ 𝔸₂[k],
          t ≫ Etale.artinSchreierMapProd k = Y.hom ≫ h ∧
          ∀ a : k × k, (σ (Multiplicative.ofAdd a)).asIso.hom.left ≫ t =
            t ≫ Etale.artinSchreierTranslationProd k a := by
  let q := Etale.artinSchreierMapProd k
  let Y : Over X := Over.mk (pullback.snd q h)
  have : Etale q :=
    MorphismProperty.pullbackMap (P := @Etale) (AffineSpace.finiteField_artinSchreier_map k).2.1
      (AffineSpace.finiteField_artinSchreier_map k).2.1
      (AffineSpace.artinSchreierMap_over _ _ _).symm
      (AffineSpace.artinSchreierMap_over _ _ _).symm
  have : Surjective q := ⟨surjective_artinSchreierMapProd⟩
  let σ : Multiplicative (k × k) →* Aut Y :=
    ((Over.pullback h).mapAut (Over.mk q)).comp (universalAction k)
  have hfst (a : k × k) : (σ (Multiplicative.ofAdd a)).asIso.hom.left ≫ pullback.fst q h =
      pullback.fst q h ≫ artinSchreierTranslationProd k a := by
    change pullback.lift _ _ _ ≫ _ = _
    exact pullback.lift_fst _ _ _
  have hsnd (a : k × k) : (σ (Multiplicative.ofAdd a)).asIso.hom.left ≫ pullback.snd q h =
      pullback.snd q h := by
    change pullback.lift _ _ _ ≫ _ = _
    exact pullback.lift_snd _ _ _
  refine ⟨Y, inferInstanceAs (IsFinite (pullback.snd q h)),
    inferInstanceAs (Etale (pullback.snd q h)),
    (pullback.snd q h).surjective, σ, ?_, pullback.fst q h, pullback.condition, hfst⟩
  intro Ω _ _ s t hst
  change s ≫ pullback.snd q h = t ≫ pullback.snd q h at hst
  obtain ⟨a, ha⟩ := exists_eq_comp_artinSchreierTranslationProd
    (s ≫ pullback.fst q h) (t ≫ pullback.fst q h) (by
      change (s ≫ pullback.fst q h) ≫ q = (t ≫ pullback.fst q h) ≫ q
      simp only [Category.assoc, pullback.condition]
      simpa only [Category.assoc] using congrArg (· ≫ h) hst)
  refine ⟨a, pullback.hom_ext ?_ ?_⟩
  · simpa only [Category.assoc, hfst] using ha
  · simpa only [Category.assoc, hsnd] using hst

private theorem tensor_comp_smul {X Y : Scheme.{u}} (π : Y ⟶ X)
    {L M : modules Λ X}
    (φ : L ⟶ (CondensedRing.lowerStar Λ π).obj (reg Λ Y))
    (ψ : M ⟶ (CondensedRing.lowerStar Λ π).obj (reg Λ Y))
    (τ : Y ⟶ Y) (hτ : τ ≫ π = π) (c d : MonObj.Γ Λ)
    (hφ : φ ≫ mapOver Λ π π τ hτ = c • φ)
    (hψ : ψ ≫ mapOver Λ π π τ hτ = d • ψ) :
    ((φ ⊗ₘ ψ) ≫ pushMul Λ π) ≫ mapOver Λ π π τ hτ =
      (c * d) • ((φ ⊗ₘ ψ) ≫ pushMul Λ π) := by
  have : MonoidalLinear (MonObj.Γ Λ) (modules Λ X) :=
    Mod.monoidalLinearOfRingHom (scalars Λ X)
  rw [Category.assoc, pushMul_deck, ← Category.assoc,
    tensorHom_comp_tensorHom, hφ, hψ]
  simp only [MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight,
    MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul,
    smul_smul, mul_comm d]

private theorem eigenmap_of_smul {X : Scheme.{u}} (Y : Over X)
    {G : Type u} [AddCommGroup G] [Fintype G]
    (σ : Multiplicative G →* Aut Y) (χ : AddChar G (MonObj.Γ Λ))
    {F : modules Λ X} (φ : F ⟶ (CondensedRing.lowerStar Λ Y.hom).obj (reg Λ Y.left))
    (hφ : ∀ a : G, φ ≫ mapOver Λ Y.hom Y.hom
      (σ (Multiplicative.ofAdd a)).asIso.hom.left (Over.w _) = χ a • φ)
    [IsIso ((CondensedRing.upperStar Λ Y.hom).map φ ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ Y.hom).counit.app (reg Λ Y.left))] :
    CondensedEigenmap Λ Y G σ χ φ := by
  dsimp only [CondensedEigenmap, condensedUnit]
  constructor
  · intro a
    rw [pull_eq_mapOver, scalarEnd, Functor.map_smul, CategoryTheory.Functor.map_id,
      Linear.comp_smul, Category.comp_id]
    exact hφ a
  · infer_instance

-- Give the universal inclusion its concrete direct-image type before transporting it.
private def asInclusion (ψ : AddChar k (MonObj.Γ Λ)) :
    ProEtale.condensedArtinSchreierSheaf Λ k ψ ⟶
      (CondensedRing.lowerStar Λ
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).obj
        (reg Λ (𝔸₁[k])) :=
  image.ι (ProEtale.condensedArtinSchreierProjector Λ k ψ).asHom

private theorem asInclusion_evaluation
    [Invertible (Fintype.card k : MonObj.Γ Λ)] (ψ : AddChar k (MonObj.Γ Λ)) :
    IsIso ((CondensedRing.upperStar Λ
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
        (asInclusion Λ k ψ) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).counit.app
        (reg Λ (𝔸₁[k]))) := by
  dsimp only [asInclusion, ProEtale.condensedArtinSchreierSheaf, reg]
  exact ProEtale.condensedArtinSchreierProjector_evaluation Λ k ψ

private theorem asRootMap_comp
    [Invertible (Fintype.card k : MonObj.Γ Λ)]
    {X Y : Scheme.{u}} (π : Y ⟶ X) (v : X ⟶ 𝔸₁[k])
    (r : Y ⟶ 𝔸₁[k])
    (hr : r ≫ AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k) = π ≫ v)
    (ψ : AddChar k (MonObj.Γ Λ)) (τ : Y ⟶ Y) (hτ : τ ≫ π = π) (b : k)
    (hb : τ ≫ r = r ≫ Etale.artinSchreierTranslation k b) :
    rootMap Λ π v
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)) r hr
      (L := ProEtale.condensedArtinSchreierSheaf Λ k ψ) (asInclusion Λ k ψ) ≫ mapOver Λ π π τ hτ =
      ψ b • rootMap Λ π v
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)) r hr
      (L := ProEtale.condensedArtinSchreierSheaf Λ k ψ) (asInclusion Λ k ψ) := by
  apply rootMap_comp Λ π v
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)) r hr
    (L := ProEtale.condensedArtinSchreierSheaf Λ k ψ) (asInclusion Λ k ψ)
    τ hτ (Etale.artinSchreierTranslation k b)
    (Etale.artinSchreierTranslation_comp_artinSchreierMap k b) (ψ b) hb
  rw [← translation_mapOver]
  simpa only [asInclusion, ProEtale.condensedArtinSchreierSheaf] using image_eigen Λ k ψ b

@[irreducible] private def rootTrivialization {X Y A : Scheme.{u}}
    (π : Y ⟶ X) (v : X ⟶ A) (q : A ⟶ A)
    (r : Y ⟶ A) (h : r ≫ q = π ≫ v) {L : modules Λ A}
    (i : L ⟶ (CondensedRing.lowerStar Λ q).obj (reg Λ A))
    (hi : IsIso ((CondensedRing.upperStar Λ q).map i ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app (reg Λ A))) :
    (CondensedRing.upperStar Λ π).obj ((CondensedRing.upperStar Λ v).obj L) ≅ reg Λ Y := by
  let := hi
  exact (CondensedRing.upperStarComp Λ π v).symm.app L ≪≫
    eqToIso (congrArg (fun w : Y ⟶ A ↦ (CondensedRing.upperStar Λ w).obj L) h.symm) ≪≫
    (CondensedRing.upperStarComp Λ r q).app L ≪≫
    (CondensedRing.upperStar Λ r).mapIso (asIso
      ((CondensedRing.upperStar Λ q).map i ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app (reg Λ A))) ≪≫
    regularPullIso Λ r

private theorem rootTrivialization_eq {X Y A : Scheme.{u}}
    (π : Y ⟶ X) (v : X ⟶ A) (q : A ⟶ A)
    (r : Y ⟶ A) (h : r ≫ q = π ≫ v) {L : modules Λ A}
    (i : L ⟶ (CondensedRing.lowerStar Λ q).obj (reg Λ A))
    (hi : IsIso ((CondensedRing.upperStar Λ q).map i ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app (reg Λ A))) :
    (CondensedRing.upperStar Λ π).map (rootMap Λ π v q r h i) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y) =
        (rootTrivialization Λ π v q r h i hi).hom := by
  rw [rootMap_adjoint, reassoc_of% (sheet_evaluation Λ q r (π ≫ v) h i)]
  simp only [rootTrivialization, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    eqToIso.hom, Functor.mapIso_hom, asIso_hom]

private theorem isIso_of_eq {C : Type*} [Category C] {M N : C}
    {f g : M ⟶ N} (h : f = g) (hg : IsIso g) : IsIso f := by
  cases h
  exact hg

private theorem rootMap_adjoint_iso {X Y A : Scheme.{u}}
    (π : Y ⟶ X) (v : X ⟶ A) (q : A ⟶ A)
    (r : Y ⟶ A) (h : r ≫ q = π ≫ v) {L : modules Λ A}
    (i : L ⟶ (CondensedRing.lowerStar Λ q).obj (reg Λ A))
    (hi : IsIso ((CondensedRing.upperStar Λ q).map i ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app (reg Λ A))) :
    IsIso ((CondensedRing.upperStar Λ π).map (rootMap Λ π v q r h i) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y)) := by
  exact isIso_of_eq (rootTrivialization_eq Λ π v q r h i hi) inferInstance

private theorem asRootMap_isIso
    [Invertible (Fintype.card k : MonObj.Γ Λ)]
    {X Y : Scheme.{u}} (π : Y ⟶ X) (v : X ⟶ 𝔸₁[k])
    (r : Y ⟶ 𝔸₁[k])
    (hr : r ≫ AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k) = π ≫ v)
    (ψ : AddChar k (MonObj.Γ Λ)) :
    IsIso ((CondensedRing.upperStar Λ π).map (rootMap Λ π v
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)) r hr
      (L := ProEtale.condensedArtinSchreierSheaf Λ k ψ) (asInclusion Λ k ψ)) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y)) := by
  exact rootMap_adjoint_iso Λ π v
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)) r hr
    (L := ProEtale.condensedArtinSchreierSheaf Λ k ψ) (asInclusion Λ k ψ)
    (asInclusion_evaluation Λ k ψ)


private def functionRootMap
    {X Y : Scheme.{u}} (π : Y ⟶ X) (v v' : X ⟶ 𝔸₁[k]) (e : v = v')
    (r : Y ⟶ 𝔸₁[k])
    (hr : r ≫ AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k) = π ≫ v')
    (ψ : AddChar k (MonObj.Γ Λ)) :
    (CondensedRing.upperStar Λ v).obj (ProEtale.condensedArtinSchreierSheaf Λ k ψ) ⟶
      (CondensedRing.lowerStar Λ π).obj (reg Λ Y) :=
  eqToHom (congrArg (fun w : X ⟶ 𝔸₁[k] ↦
    (CondensedRing.upperStar Λ w).obj (ProEtale.condensedArtinSchreierSheaf Λ k ψ)) e) ≫
    rootMap Λ π v'
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)) r hr
      (L := ProEtale.condensedArtinSchreierSheaf Λ k ψ) (asInclusion Λ k ψ)

private theorem functionRootMap_comp
    [Invertible (Fintype.card k : MonObj.Γ Λ)]
    {X Y : Scheme.{u}} (π : Y ⟶ X) (v v' : X ⟶ 𝔸₁[k]) (e : v = v')
    (r : Y ⟶ 𝔸₁[k])
    (hr : r ≫ AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k) = π ≫ v')
    (ψ : AddChar k (MonObj.Γ Λ)) (τ : Y ⟶ Y) (hτ : τ ≫ π = π) (b : k)
    (hb : τ ≫ r = r ≫ Etale.artinSchreierTranslation k b) :
    functionRootMap Λ k π v v' e r hr ψ ≫ mapOver Λ π π τ hτ =
      ψ b • functionRootMap Λ k π v v' e r hr ψ := by
  subst v'
  simpa only [functionRootMap, eqToHom_refl, Category.id_comp] using
    asRootMap_comp Λ k π v r hr ψ τ hτ b hb


private theorem functionRootMap_isIso
    [Invertible (Fintype.card k : MonObj.Γ Λ)]
    {X Y : Scheme.{u}} (π : Y ⟶ X) (v v' : X ⟶ 𝔸₁[k]) (e : v = v')
    (r : Y ⟶ 𝔸₁[k])
    (hr : r ≫ AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k) = π ≫ v')
    (ψ : AddChar k (MonObj.Γ Λ)) :
    IsIso ((CondensedRing.upperStar Λ π).map (functionRootMap Λ k π v v' e r hr ψ) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ π).counit.app (reg Λ Y)) := by
  subst v'
  simpa only [functionRootMap, eqToHom_refl, Category.id_comp] using
    asRootMap_isIso Λ k π v r hr ψ


/- Package each root map as a witness before combining the three function sheaves. -/
private theorem rootMapForFunction
    [Invertible (Fintype.card k : MonObj.Γ Λ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] (Y : Over X)
    (f : Γ(X, ⊤)) (v : X ⟶ 𝔸₁[k])
    (e : (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f) = v)
    (r : Y.left ⟶ 𝔸₁[k])
    (hr : r ≫ AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k) =
      Y.hom ≫ v)
    (ψ : AddChar k (MonObj.Γ Λ)) (σ : Multiplicative (k × k) →* Aut Y)
    (b : k × k → k)
    (hb : ∀ a, (σ (Multiplicative.ofAdd a)).asIso.hom.left ≫ r =
      r ≫ Etale.artinSchreierTranslation k (b a)) :
    ∃ φ : ProEtale.condensedArtinSchreierSheafOf Λ k X ψ f ⟶
        (CondensedRing.lowerStar Λ Y.hom).obj (reg Λ Y.left),
      (∀ a, φ ≫ mapOver Λ Y.hom Y.hom
        (σ (Multiplicative.ofAdd a)).asIso.hom.left (Over.w _) = ψ (b a) • φ) ∧
      IsIso ((CondensedRing.upperStar Λ Y.hom).map φ ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ Y.hom).counit.app (reg Λ Y.left)) := by
  refine ⟨functionRootMap Λ k Y.hom _ v e r hr ψ, ?_, ?_⟩
  · intro a
    exact functionRootMap_comp Λ k Y.hom _ v e r hr ψ _ (Over.w _) _ (hb a)
  · exact functionRootMap_isIso Λ k Y.hom _ v e r hr ψ

private theorem pairFunctionMap (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f g : Γ(X, ⊤)) :
    ∃ h : X ⟶ 𝔸₂[k],
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f) = h ≫ pullback.fst _ _ ∧
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ g) = h ≫ pullback.snd _ _ ∧
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f + g) =
        h ≫ AffineSpace.add PUnit (Spec (.of k)) := by
    refine ⟨pullback.lift (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f)
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ g) (by simp),
      (pullback.lift_fst _ _ _).symm, (pullback.lift_snd _ _ _).symm, ?_⟩
    rw [AffineSpace.add, AffineSpace.comp_homOfVector]
    simp only [pullback.lift_fst_assoc, AffineSpace.homOfVector_over]
    congr 1
    ext
    simp only [Function.comp_apply, map_add, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, pullback.lift_fst, pullback.lift_snd,
      AffineSpace.homOfVector_appTop_coord]

private theorem combineRootMaps {X : Scheme.{u}} (Y : Over X)
    (ψ : AddChar k (MonObj.Γ Λ)) (σ : Multiplicative (k × k) →* Aut Y)
    {L M N : modules Λ X}
    (φf : L ⟶ (CondensedRing.lowerStar Λ Y.hom).obj (reg Λ Y.left))
    (φg : M ⟶ (CondensedRing.lowerStar Λ Y.hom).obj (reg Λ Y.left))
    (φs : N ⟶ (CondensedRing.lowerStar Λ Y.hom).obj (reg Λ Y.left))
    (hφf : ∀ a : k × k, φf ≫ mapOver Λ Y.hom Y.hom
      (σ (Multiplicative.ofAdd a)).asIso.hom.left (Over.w _) = ψ a.1 • φf)
    (hφg : ∀ a : k × k, φg ≫ mapOver Λ Y.hom Y.hom
      (σ (Multiplicative.ofAdd a)).asIso.hom.left (Over.w _) = ψ a.2 • φg)
    (hφs : ∀ a : k × k, φs ≫ mapOver Λ Y.hom Y.hom
      (σ (Multiplicative.ofAdd a)).asIso.hom.left (Over.w _) = ψ (a.1 + a.2) • φs)
    [IsIso ((CondensedRing.upperStar Λ Y.hom).map φf ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ Y.hom).counit.app (reg Λ Y.left))]
    [IsIso ((CondensedRing.upperStar Λ Y.hom).map φg ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ Y.hom).counit.app (reg Λ Y.left))]
    [IsIso ((CondensedRing.upperStar Λ Y.hom).map φs ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ Y.hom).counit.app (reg Λ Y.left))] :
    ∃ φ₁ : L ⊗ M ⟶ (CondensedRing.lowerStar Λ Y.hom).obj (reg Λ Y.left),
    ∃ φ₂ : N ⟶ (CondensedRing.lowerStar Λ Y.hom).obj (reg Λ Y.left),
      CondensedEigenmap Λ Y (k × k) σ (tensorAddCharacter ψ) φ₁ ∧
      CondensedEigenmap Λ Y (k × k) σ (tensorAddCharacter ψ) φ₂ := by
  let φ := (φf ⊗ₘ φg) ≫ pushMul Λ Y.hom
  refine ⟨φ, φs, ?_, ?_⟩
  · have : IsIso ((CondensedRing.upperStar Λ Y.hom).map φ ≫
        (CondensedRing.upperStarLowerStarAdjunction Λ Y.hom).counit.app
          (reg Λ Y.left)) := tensor_adjoint_isIso Λ Y.hom φf φg
    apply eigenmap_of_smul
    intro a
    exact tensor_comp_smul Λ Y.hom φf φg _ (Over.w _) _ _ (hφf a) (hφg a)
  · apply eigenmap_of_smul
    intro a
    change φs ≫ mapOver Λ Y.hom Y.hom
      (σ (Multiplicative.ofAdd a)).asIso.hom.left (Over.w _) = (ψ a.1 * ψ a.2) • φs
    simpa only [AddChar.map_add_eq_mul] using hφs a

-- The nontriviality hypothesis is part of the recorded statement but is not needed.
set_option linter.unusedVariables false in
/-- The tensor sheaf and the sum-function sheaf have normalized eigenmaps into the
same finite etale direct image, with character (a,b) ↦ ψ(a)ψ(b).
Source: blueprint lemma-artin-schreier-character-sheaf Step 5, root addition and eigen-generators
(blueprint: lem-fd-as-tensor-eigenmaps).

Proof: reuse the universal product geometry `artinSchreierMapProd`,
`artinSchreierTranslationProd`, their composition and addition laws, and geometric
transitivity from the ordinary source module. Pull the product torsor back along (f,g).
Equivalently Y is the product over X of the covers y^q-y=f and z^q-z=g; it is finite
etale and surjective, with the pulled-back translation action of k times k.
The root equations identify pullbacks of the three function sheaves with pullbacks
of the universal character image along y, z and y+z. Pull back the universal counit
evaluation, already an isomorphism by condensedArtinSchreierProjector_evaluation, to
obtain maps α_f, α_g and α_sum to the regular coefficient module on Y. Define φ₁ as
the adjoint of α_f tensor α_g followed by the regular-module unit isomorphism, using
strong monoidality of pullback; define φ₂ as the adjoint of α_sum. The source root
translation identities and the deck-evaluation equation give eigencharacters ψ(a)ψ(b)
and ψ(a+b), equal by additivity. Composition comparisons identify the adjoints with
the constructed α maps by the adjunction triangular identities. These are isomorphisms,
as is their tensor, which proves both adjoint clauses. Empty schemes and p=2 are included. -/
theorem condensed_artinSchreier_tensor_eigenmaps
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    (ψ : AddChar k (MonObj.Γ Λ)) (hψ : ψ ≠ 1)
    (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f g : Γ(X, ⊤)) :
    ∃ Y : Over X, IsFinite Y.hom ∧ Etale Y.hom ∧
      Function.Surjective Y.hom.base ∧
      ∃ σ : Multiplicative (k × k) →* Aut Y,
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (s t : Spec (.of Ω) ⟶ Y.left), s ≫ Y.hom = t ≫ Y.hom →
            ∃ a : k × k, s = t ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left) ∧
        ∃ φ₁ : ProEtale.condensedArtinSchreierSheafOf Λ k X ψ f ⊗
            ProEtale.condensedArtinSchreierSheafOf Λ k X ψ g ⟶
            (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left),
        ∃ φ₂ : ProEtale.condensedArtinSchreierSheafOf Λ k X ψ (f + g) ⟶
            (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left),
          CondensedEigenmap Λ Y (k × k) σ (tensorAddCharacter ψ) φ₁ ∧
          CondensedEigenmap Λ Y (k × k) σ (tensorAddCharacter ψ) φ₂ := by
  classical
  let : Invertible (Fintype.card k : MonObj.Γ Λ) := hq.invertible
  obtain ⟨h, hf, hg, hm⟩ := pairFunctionMap k X f g
  obtain ⟨Y, hfin, het, hsurj, σ, htrans, t, ht, hτt⟩ := coverGeometry k X h
  refine ⟨Y, hfin, het, hsurj, σ, htrans, ?_⟩
  let q := AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)
  let p₁ : 𝔸₂[k] ⟶ 𝔸₁[k] := pullback.fst _ _
  let p₂ : 𝔸₂[k] ⟶ 𝔸₁[k] := pullback.snd _ _
  let m : 𝔸₂[k] ⟶ 𝔸₁[k] := AffineSpace.add PUnit (Spec (.of k))
  have hr₁ : (t ≫ p₁) ≫ q = Y.hom ≫ (h ≫ p₁) := by
    dsimp only [q, p₁]
    rw [Category.assoc, ← Etale.artinSchreierMapProd_fst,
      ← Category.assoc, ht, Category.assoc]
  have hr₂ : (t ≫ p₂) ≫ q = Y.hom ≫ (h ≫ p₂) := by
    dsimp only [q, p₂]
    rw [Category.assoc, ← Etale.artinSchreierMapProd_snd,
      ← Category.assoc, ht, Category.assoc]
  have hr₃ : (t ≫ m) ≫ q = Y.hom ≫ (h ≫ m) := by
    dsimp only [q, m]
    rw [Category.assoc, Etale.add_comp_artinSchreierMap,
      ← Category.assoc, ht, Category.assoc]
  have hc₁ (a : k × k) : (σ (Multiplicative.ofAdd a)).asIso.hom.left ≫ (t ≫ p₁) =
      (t ≫ p₁) ≫ Etale.artinSchreierTranslation k a.1 := by
    dsimp only [p₁]
    rw [← Category.assoc, hτt, Category.assoc,
      Etale.artinSchreierTranslationProd_fst, Category.assoc]
  have hc₂ (a : k × k) : (σ (Multiplicative.ofAdd a)).asIso.hom.left ≫ (t ≫ p₂) =
      (t ≫ p₂) ≫ Etale.artinSchreierTranslation k a.2 := by
    dsimp only [p₂]
    rw [← Category.assoc, hτt, Category.assoc,
      Etale.artinSchreierTranslationProd_snd, Category.assoc]
  have hc₃ (a : k × k) : (σ (Multiplicative.ofAdd a)).asIso.hom.left ≫ (t ≫ m) =
      (t ≫ m) ≫ Etale.artinSchreierTranslation k (a.1 + a.2) := by
    dsimp only [m]
    rw [← Category.assoc, hτt, Category.assoc,
      Etale.artinSchreierTranslationProd_comp_add, Category.assoc]
  obtain ⟨φf, hφf, hfIso⟩ := rootMapForFunction Λ k Y f (h ≫ p₁) hf
    (t ≫ p₁) hr₁ ψ σ Prod.fst hc₁
  obtain ⟨φg, hφg, hgIso⟩ := rootMapForFunction Λ k Y g (h ≫ p₂) hg
    (t ≫ p₂) hr₂ ψ σ Prod.snd hc₂
  obtain ⟨φs, hφs, hsIso⟩ := rootMapForFunction Λ k Y (f + g) (h ≫ m) hm
    (t ≫ m) hr₃ ψ σ (fun a ↦ a.1 + a.2) hc₃
  exact combineRootMaps Λ k Y ψ σ φf φg φs hφf hφg hφs

end AlgebraicGeometry.ArtinSchreierTrace
