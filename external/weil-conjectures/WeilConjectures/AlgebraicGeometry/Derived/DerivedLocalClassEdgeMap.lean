/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeData
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.LeftExactHomologyEdge
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf

/-! # The module edge constructed on the fixed K-injective resolution

Source: Stacks Project, cohomology.tex, Tags 0BKJ and 079W.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace AlgebraicGeometry

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

private theorem resolution_comparison_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (a : I ⟶ J) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map a) ≫
        (F.rightDerivedFunctorObjQIso J).hom =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) := by
  let π := HomotopyCategory.quotient C (.up ℤ)
  let η := F.rightDerivedFunctorUnit
  have sq₁ : CommSq (DerivedCategory.Q.map a)
      ((DerivedCategory.quotientCompQhIso C).inv.app I)
      ((DerivedCategory.quotientCompQhIso C).inv.app J)
      (DerivedCategory.Qh.map (π.map a)) :=
    ⟨DerivedCategory.quotientCompQhIso_inv_naturality a⟩
  have su : CommSq (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (π.map a)))
      (asIso (η.app (π.obj I))).hom (asIso (η.app (π.obj J))).hom
      (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (π.map a))) :=
    ⟨η.naturality (π.map a)⟩
  have sq₃ : CommSq (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (π.map a)))
      ((DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I))
      ((DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J))
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a)) :=
    ⟨DerivedCategory.quotientCompQhIso_hom_naturality
      ((F.mapHomologicalComplex (.up ℤ)).map a)⟩
  simpa only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, Category.assoc, Iso.app_inv, Iso.app_hom, π, η] using
    (((sq₁.map F.rightDerivedFunctor).vert_comp su.vert_inv).vert_comp sq₃).w

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Direct image preserves kernels because it is the right adjoint of module pullback.
Source: Stacks, Tag 0096 (blueprint: def-weil-pbc-resolution-local-class-edge). -/
instance localClassEdge_preservesFiniteLimits {T S : Scheme.{u}} (g : T ⟶ S) :
    PreservesFiniteLimits (RingedSpace.moduleDirectImage g.toLRSHom.toShHom) := by
  change PreservesFiniteLimits (Scheme.Modules.pushforward g)
  let a := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let := a.isRightAdjoint
  infer_instance

/-- Identify derived homology with the homology of the fixed representative.
Source: Stacks, Tag 079W (blueprint: def-weil-pbc-resolution-local-class-edge). -/
def localClassResolutionHomologyIso (X : Scheme.{u}) (q : ℤ)
    (K : schemeDerivedCategory X) :
    (DerivedCategory.homologyFunctor _ q).obj K ≅
      (RingedSpace.topEdgeResolution X.toRingedSpace K).homology q :=
  (DerivedCategory.homologyFunctor _ q).mapIso
      (RingedSpace.topEdgeResolutionIso X.toRingedSpace K).symm ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _

/-- Identify derived direct-image homology with the homology of the direct-image complex.
Source: Stacks, Tag 079W (blueprint: def-weil-pbc-resolution-local-class-edge). -/
def localClassDirectImageHomologyIso {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (K : schemeDerivedCategory T) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).obj
        ((schemeDerivedDirectImage g).obj K) ≅
      (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (RingedSpace.topEdgeResolution T.toRingedSpace K)).homology q :=
  (DerivedCategory.homologyFunctor _ q).mapIso
      ((schemeDerivedDirectImage g).mapIso
        (RingedSpace.topEdgeResolutionIso T.toRingedSpace K).symm ≪≫
          (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorObjQIso _) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _

/-- The actual module edge: preserve the kernel of the outgoing differential and
then descend its map to cohomology classes through the incoming boundaries.
Source: Stacks, Tags 0BKJ and 079W
(blueprint: def-weil-pbc-resolution-local-class-edge). -/
def resolutionLocalClassEdge {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    (K : schemeDerivedCategory T) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).obj
        ((schemeDerivedDirectImage g).obj K) ⟶
      (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).obj
        ((DerivedCategory.homologyFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj K) :=
  (localClassDirectImageHomologyIso g q K).hom ≫
    ShortComplex.leftExactHomologyEdge (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
      ((RingedSpace.topEdgeResolution T.toRingedSpace K).sc q) ≫
    (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).map
      (localClassResolutionHomologyIso T q K).inv

private theorem resolution_homology_square (X : Scheme.{u}) (q : ℤ)
    {K L : schemeDerivedCategory X} (k : K ⟶ L)
    (b : RingedSpace.topEdgeResolution X.toRingedSpace K ⟶
      RingedSpace.topEdgeResolution X.toRingedSpace L)
    (hb : DerivedCategory.Q.map b =
      (RingedSpace.topEdgeResolutionIso X.toRingedSpace K).hom ≫ k ≫
        (RingedSpace.topEdgeResolutionIso X.toRingedSpace L).inv) :
    (DerivedCategory.homologyFunctor _ q).map k ≫
        (localClassResolutionHomologyIso X q L).hom =
      (localClassResolutionHomologyIso X q K).hom ≫ HomologicalComplex.homologyMap b q := by
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q
  have hr : k ≫ (RingedSpace.topEdgeResolutionIso X.toRingedSpace L).inv =
      (RingedSpace.topEdgeResolutionIso X.toRingedSpace K).inv ≫ DerivedCategory.Q.map b := by
    simp only [hb, Iso.inv_hom_id_assoc]
  have hn := (DerivedCategory.homologyFunctorFactors _ q).hom.naturality b
  dsimp only [localClassResolutionHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Functor.comp_obj, Functor.comp_map,
    HomologicalComplex.homologyFunctor_obj, HomologicalComplex.homologyFunctor_map] at *
  change H.map k ≫ (H.map _ ≫ _) = (H.map _ ≫ _) ≫ _
  rw [← Category.assoc, ← H.map_comp, hr, H.map_comp, Category.assoc]
  exact congrArg (fun z ↦ H.map _ ≫ z) hn

private theorem directImage_homology_square {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    {K L : schemeDerivedCategory T} (k : K ⟶ L)
    (b : RingedSpace.topEdgeResolution T.toRingedSpace K ⟶
      RingedSpace.topEdgeResolution T.toRingedSpace L)
    (hb : DerivedCategory.Q.map b =
      (RingedSpace.topEdgeResolutionIso T.toRingedSpace K).hom ≫ k ≫
        (RingedSpace.topEdgeResolutionIso T.toRingedSpace L).inv) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map
        ((schemeDerivedDirectImage g).map k) ≫
        (localClassDirectImageHomologyIso g q L).hom =
      (localClassDirectImageHomologyIso g q K).hom ≫
        HomologicalComplex.homologyMap
          (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
            (.up ℤ)).map b) q := by
  let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let R := schemeDerivedDirectImage g
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  have hr : k ≫ (RingedSpace.topEdgeResolutionIso T.toRingedSpace L).inv =
      (RingedSpace.topEdgeResolutionIso T.toRingedSpace K).inv ≫ DerivedCategory.Q.map b := by
    simp only [hb, Iso.inv_hom_id_assoc]
  have h₁ := congrArg R.map hr
  simp only [Functor.map_comp] at h₁
  have h₂ := resolution_comparison_naturality F b
  have h₃ := (DerivedCategory.homologyFunctorFactors _ q).hom.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map b)
  have hs := ((CommSq.mk h₁).vert_comp (CommSq.mk h₂)).map H
  have hh := (hs.vert_comp (CommSq.mk h₃)).w
  simpa only [localClassDirectImageHomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Iso.symm_hom, Category.assoc, Iso.app_hom,
    Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
    HomologicalComplex.homologyFunctor_map] using hh

/-- The constructed edge is natural in every derived morphism.
Source: Stacks, Tags 0BKJ and 079W
(blueprint: def-weil-pbc-resolution-local-class-edge). -/
theorem resolutionLocalClassEdge_naturality {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    {K L : schemeDerivedCategory T} (k : K ⟶ L) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map
        ((schemeDerivedDirectImage g).map k) ≫
        resolutionLocalClassEdge g q L =
      resolutionLocalClassEdge g q K ≫ (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).map
        ((DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).map k) := by
  obtain ⟨b, hb⟩ := RingedSpace.exists_complex_map_into_kInjective
    (RingedSpace.topEdgeResolution T.toRingedSpace K)
    (RingedSpace.topEdgeResolution T.toRingedSpace L)
    ((RingedSpace.topEdgeResolutionIso T.toRingedSpace K).hom ≫ k ≫
      (RingedSpace.topEdgeResolutionIso T.toRingedSpace L).inv)
  let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  have h₁ := directImage_homology_square g q k b hb
  have h₂ := ShortComplex.leftExactHomologyEdge_naturality F
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) q).map b)
  have h₃ := resolution_homology_square T q k b hb
  have hi : HomologicalComplex.homologyMap b q ≫
      (localClassResolutionHomologyIso T q L).inv =
    (localClassResolutionHomologyIso T q K).inv ≫
      (DerivedCategory.homologyFunctor _ q).map k := by
    apply (Iso.eq_inv_comp (localClassResolutionHomologyIso T q K)).2
    rw [← Category.assoc, ← h₃, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change _ ≫ (_ ≫ _ ≫ _) = (_ ≫ _ ≫ _) ≫ _
  rw [← Category.assoc, ← Category.assoc, h₁, Category.assoc, Category.assoc]
  erw [reassoc_of% h₂]
  simpa only [Functor.map_comp, Category.assoc, HomologicalComplex.homologyMap,
    HomologicalComplex.sc, F] using
    congrArg (fun z ↦ (localClassDirectImageHomologyIso g q K).hom ≫
      ShortComplex.leftExactHomologyEdge F
        ((RingedSpace.topEdgeResolution T.toRingedSpace K).sc q) ≫ F.map z) hi

end AlgebraicGeometry
