/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift

/-! # Signed shifts of a representative-normalized tensor comparison

## References

* Stacks Project, Cohomology on Sites, Tag 07A4
* More on Algebra, Tag 0FNH
* Stacks Project, Tags 07A4 and 0FNH, item-shift-tensor
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

-- The pure-unit formula determines naturality of the ordinary comparison.
private theorem ordinary_naturality (o : Operation F R S) (mu : o.OrdinaryTensor)
    {M M' N N' : Mod R} (f : M ⟶ M') (g : N ⟶ N') :
    o.pullback.map (((tensor R).map f).app N ≫ ((tensor R).obj M').map g) ≫
      (mu.iso M' N').hom =
    (mu.iso M N).hom ≫ (((tensor S).map (o.pullback.map f)).app (o.pullback.obj N) ≫
      ((tensor S).obj (o.pullback.obj M')).map (o.pullback.map g)) := by
  apply (o.moduleAdjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [o.pushforward.map_comp, o.pushforward.map_comp]
  have hn := o.moduleAdjunction.unit.naturality
    (((tensor R).map f).app N ≫ ((tensor R).obj M').map g)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, ← hn]
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext R M N
  intro W x y
  have hp := SheafOfModules.CochainScalarConstruction.pure_map R f g W x y
  change _ = pure R M' N' W (f.val.app W x) (g.val.app W y) at hp
  have hM := congrArg (fun k ↦ k.val.app W x) (o.moduleAdjunction.unit.naturality f)
  have hN := congrArg (fun k ↦ k.val.app W y) (o.moduleAdjunction.unit.naturality g)
  change _ = _ at hM hN
  have hS := SheafOfModules.CochainScalarConstruction.pure_map S
    (o.pullback.map f) (o.pullback.map g) (F.op.obj W)
    ((o.moduleAdjunction.unit.app M).val.app W x)
    ((o.moduleAdjunction.unit.app N).val.app W y)
  change _ = pure S _ _ _ _ _ at hS
  simp only [MonoidalCategory.tensorHom_def] at hp hS
  change ((((tensor R).map f).app N ≫ ((tensor R).obj M').map g).val.app W)
    (pure R M N W x y) = pure R M' N' W (f.val.app W x) (g.val.app W y) at hp
  change ((((tensor S).map (o.pullback.map f)).app (o.pullback.obj N) ≫
    ((tensor S).obj (o.pullback.obj M')).map (o.pullback.map g)).val.app (F.op.obj W))
      (pure S _ _ (F.op.obj W)
        ((o.moduleAdjunction.unit.app M).val.app W x)
        ((o.moduleAdjunction.unit.app N).val.app W y)) = _ at hS
  change
    ((o.pushforward.map (mu.iso M' N').hom).val.app W)
      ((o.moduleAdjunction.unit.app _).val.app W
        (((((tensor R).map f).app N ≫ ((tensor R).obj M').map g)).val.app W
          (pure R M N W x y))) =
    ((o.pushforward.map
      (((tensor S).map (o.pullback.map f)).app (o.pullback.obj N) ≫
        ((tensor S).obj (o.pullback.obj M')).map (o.pullback.map g))).val.app W)
        (((o.pushforward.map (mu.iso M N).hom).val.app W)
          ((o.moduleAdjunction.unit.app _).val.app W (pure R M N W x y)))
  rw [hp, mu.pure_unit, mu.pure_unit]
  exact (hS.trans (congrArg₂ (pure S _ _ (F.op.obj W)) hM.symm hN.symm)).symm

private def ordinaryComparison (o : Operation F R S) (mu : o.OrdinaryTensor) :
    (Functor.postcompose₂.obj o.pullback).obj (tensor R) ≅
      (((Functor.whiskeringLeft₂ (Mod S)).obj o.pullback).obj o.pullback).obj (tensor S) :=
by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  exact NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ mu.iso M N) (fun {N N'} g ↦ by
    change o.pullback.map (((tensor R).obj M).map g) ≫ _ =
      _ ≫ ((tensor S).obj (o.pullback.obj M)).map (o.pullback.map g)
    simpa only [tensor, curriedTensor_map_app, curriedTensor_obj_map,
      CategoryTheory.Functor.map_id, MonoidalCategory.id_whiskerRight, NatTrans.id_app,
      Category.id_comp] using ordinary_naturality o mu (𝟙 M) g))
    (fun {M M'} f ↦ by
      apply NatTrans.ext
      funext N
      change o.pullback.map (((tensor R).map f).app N) ≫ _ =
        _ ≫ ((tensor S).map (o.pullback.map f)).app (o.pullback.obj N)
      have h := ordinary_naturality o mu f (𝟙 N)
      erw [((tensor R).obj M').map_id, Category.comp_id,
        o.pullback.map_id, ((tensor S).obj (o.pullback.obj M')).map_id,
        Category.comp_id] at h
      exact h)

-- Totalize the ordinary comparison; left-adjoint pullback preserves the coproducts.
private def chainComparison (o : Operation F R S) (mu : o.OrdinaryTensor) :
    (Functor.postcompose₂.obj (o.pullback.mapHomologicalComplex (.up ℤ))).obj
      ((tensor R).map₂CochainComplex) ≅
    (((Functor.whiskeringLeft₂ (CochainComplex (Mod S) ℤ)).obj
      (o.pullback.mapHomologicalComplex (.up ℤ))).obj
        (o.pullback.mapHomologicalComplex (.up ℤ))).obj ((tensor S).map₂CochainComplex) := by
  let := o.moduleAdjunction.isLeftAdjoint
  exact asIso (HomologicalComplex.mapBifunctorComparisonNatTrans
    (ordinaryComparison o mu).hom (.up ℤ))

private theorem chainComparison_inv (o : Operation F R S)
    (a : TensorModel R) (b : TensorModel S) (mu : o.OrdinaryTensor)
    (t : TensorComparison o.pullback o.leftModel a b mu.iso)
    (P Q : CochainComplex (Mod R) ℤ) :
    ((chainComparison o mu).inv.app P).app Q =
      totalMap a b o.pullback mu.iso t.comm P Q := by
  let := o.moduleAdjunction.isLeftAdjoint
  apply (cancel_epi (((chainComparison o mu).hom.app P).app Q)).1
  simp only [← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map o.pullback
  intro p q hpq
  change o.pullback.map _ ≫ 𝟙 _ =
    o.pullback.map _ ≫
      (HomologicalComplex.mapBifunctorComparison (ordinaryComparison o mu).hom
        (.up ℤ) P Q).f n ≫ totalComponent a b o.pullback mu.iso P Q n
  rw [HomologicalComplex.mapBifunctorComparison_f,
    HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  simp only [Category.comp_id, totalComponent,
    tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc]
  change _ = (mu.iso (P.X p) (Q.X q)).hom ≫ (mu.iso (P.X p) (Q.X q)).inv ≫ _
  rw [Iso.hom_inv_id_assoc]

@[no_expose] private def fixedFirst
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (G : A ⥤ B)
    (t : T ⋙ G ⟶ (G.prod G) ⋙ T') (N : A) :
    (Functor.curry.obj T).flip.obj N ⋙ G ⟶
      G ⋙ (Functor.curry.obj T').flip.obj (G.obj N) where
  app M := t.app (M, N)
  naturality {M M'} f := by
    have h := t.naturality (Prod.mkHom f (𝟙 N))
    change G.map (T.map (Prod.mkHom f (𝟙 N))) ≫ _ =
      _ ≫ T'.map (Prod.mkHom (G.map f) (G.map (𝟙 N))) at h
    simpa only [CategoryTheory.Functor.map_id, Functor.comp_map,
      Functor.flip_obj_map, Functor.curry_obj_map_app, Functor.curry_obj_obj_map] using h

@[no_expose] private def fixedSecond
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (G : A ⥤ B)
    (t : T ⋙ G ⟶ (G.prod G) ⋙ T') (M : A) :
    (Functor.curry.obj T).obj M ⋙ G ⟶
      G ⋙ (Functor.curry.obj T').obj (G.obj M) where
  app N := t.app (M, N)
  naturality {N N'} g := by
    have h := t.naturality (Prod.mkHom (𝟙 M) g)
    change G.map (T.map (Prod.mkHom (𝟙 M) g)) ≫ _ =
      _ ≫ T'.map (Prod.mkHom (G.map (𝟙 M)) (G.map g)) at h
    simpa only [CategoryTheory.Functor.map_id, Functor.comp_map,
      Functor.flip_obj_map, Functor.curry_obj_map_app, Functor.curry_obj_obj_map] using h

private theorem resolving_stable (a : TensorModel R) [sa : TensorShifts a] :
    (resolving R).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun P hp ↦ (sa.first P P hp hp n).choose⟩

-- Fix one resolving argument in the supplied representative isomorphism.
private def representativeFirst (a : TensorModel R)
    (Q : (resolving R).FullSubcategory) :
    (resolving R).ι ⋙ ((tensor R).map₂CochainComplex).flip.obj Q.obj ⋙ DerivedCategory.Q ≅
      ((resolving R).ι ⋙ DerivedCategory.Q) ⋙
        (Functor.curry.obj a.functor).flip.obj (DerivedCategory.Q.obj Q.obj) :=
  NatIso.ofComponents (fun P ↦ a.representative.app (P, Q)) (fun {P P'} f ↦ by
    have h := a.representative.hom.naturality (Prod.mkHom f (𝟙 Q))
    change DerivedCategory.Q.map
      ((((tensor R).map₂CochainComplex).map f.hom).app Q.obj ≫
        (((tensor R).map₂CochainComplex).obj P'.obj).map (𝟙 Q.obj)) ≫ _ =
      _ ≫ a.functor.map (Prod.mkHom (DerivedCategory.Q.map f.hom)
        (DerivedCategory.Q.map (𝟙 Q.obj))) at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_id] at h
    exact h)

private def representativeSecond (a : TensorModel R)
    (P : (resolving R).FullSubcategory) :
    (resolving R).ι ⋙ ((tensor R).map₂CochainComplex).obj P.obj ⋙ DerivedCategory.Q ≅
      ((resolving R).ι ⋙ DerivedCategory.Q) ⋙
        (Functor.curry.obj a.functor).obj (DerivedCategory.Q.obj P.obj) :=
  NatIso.ofComponents (fun Q ↦ a.representative.app (P, Q)) (fun {Q Q'} f ↦ by
    have h := a.representative.hom.naturality (Prod.mkHom (𝟙 P) f)
    change DerivedCategory.Q.map
      ((((tensor R).map₂CochainComplex).map (𝟙 P.obj)).app Q.obj ≫
        (((tensor R).map₂CochainComplex).obj P.obj).map f.hom) ≫ _ =
      _ ≫ a.functor.map (Prod.mkHom (DerivedCategory.Q.map (𝟙 P.obj))
        (DerivedCategory.Q.map f.hom)) at h
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      CategoryTheory.Functor.map_id] at h
    exact h)

private theorem inclusion_shift_hom [(resolving R).IsStableUnderShift ℤ]
    (P : (resolving R).FullSubcategory) (n : ℤ) :
    ((resolving R).ι.commShiftIso n).hom.app P = 𝟙 _ := rfl

private theorem representativeFirst_shift (a : TensorModel R) [sa : TensorShifts a]
    [(resolving R).IsStableUnderShift ℤ] (Q : (resolving R).FullSubcategory) :
    NatTrans.CommShift (representativeFirst a Q).hom ℤ := by
  let := sa.tensorAdditive
  let := sa.tensorObjAdditive
  constructor
  intro n
  ext P
  obtain ⟨hpn, h⟩ := sa.first P.obj Q.obj P.property Q.property n
  have hh := congrArg (fun f ↦ f ≫
    (shiftFunctor (Der R) n).map (a.representative.hom.app (P, Q))) h
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app] at hh
  erw [(shiftFunctor (Der R) n).map_id, Category.comp_id] at hh
  convert (show _ from hh.symm) using 1 <;>
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    representativeFirst, NatIso.ofComponents_hom_app,
    Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_map₂CochainComplex_flip_hom_app,
    Functor.comp_obj, inclusion_shift_hom, CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.flip_obj_map, Functor.curry_obj_map_app, Iso.app_hom, Category.assoc]
  all_goals rfl

private theorem representativeSecond_shift (a : TensorModel R) [sa : TensorShifts a]
    [(resolving R).IsStableUnderShift ℤ] (P : (resolving R).FullSubcategory) :
    NatTrans.CommShift (representativeSecond a P).hom ℤ := by
  let := sa.tensorAdditive
  let := sa.tensorObjAdditive
  constructor
  intro n
  ext Q
  obtain ⟨hqn, h⟩ := sa.second P.obj Q.obj P.property Q.property n
  have hh := congrArg (fun f ↦ f ≫
    (shiftFunctor (Der R) n).map (a.representative.hom.app (P, Q))) h
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app] at hh
  erw [(shiftFunctor (Der R) n).map_id, Category.comp_id] at hh
  convert (show _ from hh.symm) using 1 <;>
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    representativeSecond, NatIso.ofComponents_hom_app,
    Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_map₂CochainComplex_hom_app,
    Functor.comp_obj, inclusion_shift_hom, CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.curry_obj_obj_map, Iso.app_hom, Category.assoc]
  all_goals rfl

-- Only essential surjectivity is needed; no full-faithfulness theorem is used.
private theorem resolving_essSurj :
    ((resolving R).ι ⋙ DerivedCategory.Q).EssSurj := by
  constructor
  intro M
  let A := DerivedCategory.Q.objPreimage M
  obtain ⟨P, f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients A
  have := hq
  have hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hf n)
  exact ⟨⟨P, hp, hflat⟩, ⟨asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso M⟩⟩

private def reindexIso {A B E : Type*} [Category A] [Category B] [Category E]
    (P : ObjectProperty B) (H G : B ⥤ E) (r : P.ι ⋙ H ≅ P.ι ⋙ G)
    (j : A ⥤ B) (hj : ∀ X, P (j.obj X)) : j ⋙ H ≅ j ⋙ G :=
  let k := P.lift j hj
  let e := P.liftCompιIso j hj
  Functor.isoWhiskerRight e.symm H ≪≫ Functor.associator k P.ι H ≪≫
    Functor.isoWhiskerLeft k r ≪≫ (Functor.associator k P.ι G).symm ≪≫
      Functor.isoWhiskerRight e G

private theorem reindexIso_shift {A B E : Type*} [Category A] [Category B] [Category E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ]
    (P : ObjectProperty B) [P.IsStableUnderShift ℤ]
    (H G : B ⥤ E) [H.CommShift ℤ] [G.CommShift ℤ]
    (r : P.ι ⋙ H ≅ P.ι ⋙ G) [NatTrans.CommShift r.hom ℤ]
    (j : A ⥤ B) [j.CommShift ℤ] (hj : ∀ X, P (j.obj X)) :
    NatTrans.CommShift (reindexIso P H G r j hj).hom ℤ := by
  dsimp [reindexIso]
  infer_instance

private theorem reindexIso_hom_app {A B E : Type*}
    [Category A] [Category B] [Category E]
    (P : ObjectProperty B) (H G : B ⥤ E) (r : P.ι ⋙ H ≅ P.ι ⋙ G)
    (j : A ⥤ B) (hj : ∀ X, P (j.obj X)) (X : A) :
    (reindexIso P H G r j hj).hom.app X = r.hom.app ⟨j.obj X, hj X⟩ := by
  change H.map (𝟙 _) ≫ 𝟙 _ ≫ r.hom.app ⟨j.obj X, hj X⟩ ≫ 𝟙 _ ≫ G.map (𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

-- Cancel the shift-compatible outer edges of a commutative comparison diagram.
private theorem shift_of_diagram {A D E : Type*}
    [Category A] [Category D] [Category E]
    [HasShift A ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (q : A ⥤ D) [q.CommShift ℤ] (L : D ⥤ E) [L.CommShift ℤ]
    (T : D ⥤ D) [T.CommShift ℤ] (U : E ⥤ E) [U.CommShift ℤ]
    (t : T ⋙ L ⟶ L ⋙ U) (V W : A ⥤ E) [V.CommShift ℤ] [W.CommShift ℤ]
    (r : V ≅ q ⋙ (T ⋙ L)) [NatTrans.CommShift r.hom ℤ]
    (s : q ⋙ (L ⋙ U) ≅ W) [NatTrans.CommShift s.hom ℤ]
    (v : V ⟶ W) [NatTrans.CommShift v ℤ]
    (h : r.hom ≫ Functor.whiskerLeft q t ≫ s.hom = v) :
    NatTrans.CommShift (Functor.whiskerLeft q t) ℤ := by
  have ht : Functor.whiskerLeft q t = r.inv ≫ v ≫ s.inv := by
    rw [← h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [ht]
  infer_instance

private theorem representative_square (o : Operation F R S)
    (a : TensorModel R) (b : TensorModel S) (mu : o.OrdinaryTensor)
    (t : TensorComparison o.pullback o.leftModel a b mu.iso)
    (P Q : CochainComplex (Mod R) ℤ) (hp : resolving R P) (hq : resolving R Q) :
    o.left.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      t.comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      b.functor.map (Prod.mkHom (o.leftModel.factors.hom.app P)
        (o.leftModel.factors.hom.app Q)) =
    o.leftModel.factors.hom.app ((total R).obj (P, Q)) ≫
      DerivedCategory.Q.map (((chainComparison o mu).hom.app P).app Q) ≫
      b.representative.hom.app
        (⟨(o.pullback.mapHomologicalComplex (.up ℤ)).obj P, t.preserves P hp⟩,
          ⟨(o.pullback.mapHomologicalComplex (.up ℤ)).obj Q, t.preserves Q hq⟩) := by
  have h := t.representative P Q hp hq
  rw [← chainComparison_inv o a b mu t P Q] at h
  have hh := congrArg (fun z ↦ z ≫
    DerivedCategory.Q.map (((chainComparison o mu).hom.app P).app Q) ≫
      b.representative.hom.app
        (⟨(o.pullback.mapHomologicalComplex (.up ℤ)).obj P, t.preserves P hp⟩,
          ⟨(o.pullback.mapHomologicalComplex (.up ℤ)).obj Q, t.preserves Q hq⟩)) h
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app] at hh
  erw [DerivedCategory.Q.map_id] at hh
  simp only [Category.id_comp, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh

-- Elaborating the representative diagram involves many large composite functor expressions.
private theorem fixedFirst_resolving (o : Operation F R S)
    (a : TensorModel R) (b : TensorModel S) [sa : TensorShifts a] [sb : TensorShifts b]
    (mu : o.OrdinaryTensor) (t : TensorComparison o.pullback o.leftModel a b mu.iso)
    (Q : (resolving R).FullSubcategory) :
    NatTrans.CommShift
      (fixedFirst a.functor b.functor o.left t.comparison.hom (DerivedCategory.Q.obj Q.obj))
      ℤ := by
  let := resolving_stable a
  let := resolving_stable b
  let := resolving_essSurj (R := R)
  let := o.moduleAdjunction.isLeftAdjoint
  let i := (resolving R).ι
  let q := i ⋙ DerivedCategory.Q
  let LC := o.pullback.mapHomologicalComplex (.up ℤ)
  let j := i ⋙ LC
  let TR₀ := ((tensor R).map₂CochainComplex).flip.obj Q.obj
  let TR₁ := (Functor.curry.obj a.functor).flip.obj (DerivedCategory.Q.obj Q.obj)
  let TS₀ := ((tensor S).map₂CochainComplex).flip.obj (LC.obj Q.obj)
  let TS₂ := (Functor.curry.obj b.functor).flip.obj (o.left.obj (DerivedCategory.Q.obj Q.obj))
  let TS₄ := (Functor.curry.obj b.functor).flip.obj (DerivedCategory.Q.obj (LC.obj Q.obj))
  let τ := fixedFirst a.functor b.functor o.left t.comparison.hom (DerivedCategory.Q.obj Q.obj)
  let eps := o.pullback.mapDerivedCategoryFactors
  let c := chainComparison o mu
  let chi : TR₀ ⋙ LC ≅ LC ⋙ TS₀ := ((CategoryTheory.flipFunctor _ _ _).mapIso c).app Q.obj
  have : NatTrans.CommShift chi.hom ℤ := by
    exact HomologicalComplex.commShift_mapBifunctorComparisonNatTrans_flipApp
      (ordinaryComparison o mu).hom Q.obj
  let beta : TS₂ ≅ TS₄ :=
    (Functor.curry.obj b.functor).flip.mapIso (eps.app Q.obj)
  have : NatTrans.CommShift beta.hom ℤ := by dsimp [beta]; infer_instance
  let rR := Functor.associator i TR₀ DerivedCategory.Q ≪≫ representativeFirst a Q
  have : NatTrans.CommShift rR.hom ℤ := by
    have := representativeFirst_shift a Q
    dsimp [rR]
    infer_instance
  let Q' : (resolving S).FullSubcategory := ⟨LC.obj Q.obj, t.preserves _ Q.property⟩
  let rS := representativeFirst b Q' ≪≫
    Functor.associator (resolving S).ι DerivedCategory.Q TS₄
  have : NatTrans.CommShift rS.hom ℤ := by
    have := representativeFirst_shift b Q'
    dsimp [rS]
    infer_instance
  let hj : ∀ X, resolving S (j.obj X) := fun X ↦ t.preserves X.obj X.property
  let s := reindexIso (resolving S) (TS₀ ⋙ DerivedCategory.Q)
    (DerivedCategory.Q ⋙ TS₄) rS j hj
  have : NatTrans.CommShift s.hom ℤ := reindexIso_shift _ _ _ _ _ _
  let ee : q ⋙ o.left ≅ j ⋙ DerivedCategory.Q :=
    Functor.associator i DerivedCategory.Q o.left ≪≫
      Functor.isoWhiskerLeft i eps ≪≫ (Functor.associator i LC DerivedCategory.Q).symm
  have : NatTrans.CommShift ee.hom ℤ := by dsimp [ee]; infer_instance
  let r₁ := Functor.isoWhiskerRight rR o.left ≪≫ Functor.associator q TR₁ o.left
  let r₂ := (Functor.associator q o.left TS₂).symm ≪≫
    Functor.isoWhiskerRight ee TS₂ ≪≫ Functor.isoWhiskerLeft (j ⋙ DerivedCategory.Q) beta ≪≫
      Functor.associator j DerivedCategory.Q TS₄
  let w₀ := Functor.associator (i ⋙ TR₀) DerivedCategory.Q o.left ≪≫
    Functor.isoWhiskerLeft (i ⋙ TR₀) eps ≪≫
    (Functor.associator (i ⋙ TR₀) LC DerivedCategory.Q).symm
  have : NatTrans.CommShift w₀.hom ℤ := by dsimp [w₀]; infer_instance
  let w₁ := Functor.isoWhiskerRight (Functor.associator i TR₀ LC) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft i chi) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight (Functor.associator i LC TS₀).symm DerivedCategory.Q
  have : NatTrans.CommShift w₁.hom ℤ := by dsimp [w₁]; infer_instance
  let w₂ := Functor.associator j TS₀ DerivedCategory.Q ≪≫ s
  have : NatTrans.CommShift w₂.hom ℤ := by dsimp [w₂]; infer_instance
  let w := w₀ ≪≫ w₁ ≪≫ w₂
  have : NatTrans.CommShift r₁.hom ℤ := by dsimp [r₁]; infer_instance
  have : NatTrans.CommShift r₂.hom ℤ := by dsimp [r₂]; infer_instance
  have : NatTrans.CommShift w.hom ℤ := by dsimp [w]; infer_instance
  have hh : NatTrans.CommShift (Functor.whiskerLeft q τ) ℤ := by
    apply shift_of_diagram q o.left TR₁ TS₂ τ _ _ r₁ r₂ w.hom
    apply NatTrans.ext
    funext A
    have hb : TS₂.map (eps.hom.app A.obj) ≫
        beta.hom.app (DerivedCategory.Q.obj (LC.obj A.obj)) =
        b.functor.map (Prod.mkHom (eps.hom.app A.obj) (eps.hom.app Q.obj)) := by
      change b.functor.map (Prod.mkHom _ (𝟙 _)) ≫
        b.functor.map (Prod.mkHom (𝟙 _) _) = _
      rw [← b.functor.map_comp]
      congr 1
      ext <;> simp
    have hn := representative_square o a b mu t A.obj Q.obj A.property Q.property
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.flip_obj_obj,
      Functor.curry_obj_obj_obj, representativeFirst, Functor.isoWhiskerRight_trans,
      Iso.trans_assoc, Iso.trans_hom, Functor.isoWhiskerRight_hom, fixedFirst, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      CategoryTheory.Functor.map_id, NatIso.ofComponents_hom_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.flip_obj_map, NatTrans.id_app,
      Functor.curry_obj_map_app, Bifunctor.map_id, Functor.flip_map_app,
      Functor.curry_obj_obj_map, Category.comp_id, Category.id_comp, flipFunctor_obj,
      flipFunctor_map_app_app, reindexIso_hom_app, i, TR₀, j, TS₄, q, TR₁, r₁, rR, TS₂, τ, r₂,
      ee, eps, beta, w, TS₀, w₁, chi, c, w₂, s, rS, Q', w₀]
    erw [Category.id_comp, Category.id_comp, hb]
    exact hn
  exact NatTrans.CommShift.of_whiskerLeft τ q
    (fun X ↦ ⟨q.objPreimage X, (q.objObjPreimageIso X).inv, inferInstance⟩)

-- Elaborating the representative diagram involves many large composite functor expressions.
private theorem fixedSecond_resolving (o : Operation F R S)
    (a : TensorModel R) (b : TensorModel S) [sa : TensorShifts a] [sb : TensorShifts b]
    (mu : o.OrdinaryTensor) (t : TensorComparison o.pullback o.leftModel a b mu.iso)
    (Q : (resolving R).FullSubcategory) :
    NatTrans.CommShift
      (fixedSecond a.functor b.functor o.left t.comparison.hom (DerivedCategory.Q.obj Q.obj))
      ℤ := by
  let := resolving_stable a
  let := resolving_stable b
  let := resolving_essSurj (R := R)
  let := o.moduleAdjunction.isLeftAdjoint
  let i := (resolving R).ι
  let q := i ⋙ DerivedCategory.Q
  let LC := o.pullback.mapHomologicalComplex (.up ℤ)
  let j := i ⋙ LC
  let TR₀ := ((tensor R).map₂CochainComplex).obj Q.obj
  let TR₁ := (Functor.curry.obj a.functor).obj (DerivedCategory.Q.obj Q.obj)
  let TS₀ := ((tensor S).map₂CochainComplex).obj (LC.obj Q.obj)
  let TS₂ := (Functor.curry.obj b.functor).obj (o.left.obj (DerivedCategory.Q.obj Q.obj))
  let TS₄ := (Functor.curry.obj b.functor).obj (DerivedCategory.Q.obj (LC.obj Q.obj))
  let τ := fixedSecond a.functor b.functor o.left t.comparison.hom (DerivedCategory.Q.obj Q.obj)
  let eps := o.pullback.mapDerivedCategoryFactors
  let c := chainComparison o mu
  let chi : TR₀ ⋙ LC ≅ LC ⋙ TS₀ := c.app Q.obj
  have : NatTrans.CommShift chi.hom ℤ := by
    exact HomologicalComplex.commShift_mapBifunctorComparisonNatTrans_app
      (ordinaryComparison o mu).hom Q.obj
  let beta : TS₂ ≅ TS₄ :=
    (Functor.curry.obj b.functor).mapIso (eps.app Q.obj)
  have : NatTrans.CommShift beta.hom ℤ := by dsimp [beta]; infer_instance
  let rR := Functor.associator i TR₀ DerivedCategory.Q ≪≫ representativeSecond a Q
  have : NatTrans.CommShift rR.hom ℤ := by
    have := representativeSecond_shift a Q
    dsimp [rR]
    infer_instance
  let Q' : (resolving S).FullSubcategory := ⟨LC.obj Q.obj, t.preserves _ Q.property⟩
  let rS := representativeSecond b Q' ≪≫
    Functor.associator (resolving S).ι DerivedCategory.Q TS₄
  have : NatTrans.CommShift rS.hom ℤ := by
    have := representativeSecond_shift b Q'
    dsimp [rS]
    infer_instance
  let hj : ∀ X, resolving S (j.obj X) := fun X ↦ t.preserves X.obj X.property
  let s := reindexIso (resolving S) (TS₀ ⋙ DerivedCategory.Q)
    (DerivedCategory.Q ⋙ TS₄) rS j hj
  have : NatTrans.CommShift s.hom ℤ := reindexIso_shift _ _ _ _ _ _
  let ee : q ⋙ o.left ≅ j ⋙ DerivedCategory.Q :=
    Functor.associator i DerivedCategory.Q o.left ≪≫
      Functor.isoWhiskerLeft i eps ≪≫ (Functor.associator i LC DerivedCategory.Q).symm
  have : NatTrans.CommShift ee.hom ℤ := by dsimp [ee]; infer_instance
  let r₁ := Functor.isoWhiskerRight rR o.left ≪≫ Functor.associator q TR₁ o.left
  let r₂ := (Functor.associator q o.left TS₂).symm ≪≫
    Functor.isoWhiskerRight ee TS₂ ≪≫ Functor.isoWhiskerLeft (j ⋙ DerivedCategory.Q) beta ≪≫
      Functor.associator j DerivedCategory.Q TS₄
  let w₀ := Functor.associator (i ⋙ TR₀) DerivedCategory.Q o.left ≪≫
    Functor.isoWhiskerLeft (i ⋙ TR₀) eps ≪≫
    (Functor.associator (i ⋙ TR₀) LC DerivedCategory.Q).symm
  have : NatTrans.CommShift w₀.hom ℤ := by dsimp [w₀]; infer_instance
  let w₁ := Functor.isoWhiskerRight (Functor.associator i TR₀ LC) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft i chi) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight (Functor.associator i LC TS₀).symm DerivedCategory.Q
  have : NatTrans.CommShift w₁.hom ℤ := by dsimp [w₁]; infer_instance
  let w₂ := Functor.associator j TS₀ DerivedCategory.Q ≪≫ s
  have : NatTrans.CommShift w₂.hom ℤ := by dsimp [w₂]; infer_instance
  let w := w₀ ≪≫ w₁ ≪≫ w₂
  have : NatTrans.CommShift r₁.hom ℤ := by dsimp [r₁]; infer_instance
  have : NatTrans.CommShift r₂.hom ℤ := by dsimp [r₂]; infer_instance
  have : NatTrans.CommShift w.hom ℤ := by dsimp [w]; infer_instance
  have hh : NatTrans.CommShift (Functor.whiskerLeft q τ) ℤ := by
    apply shift_of_diagram q o.left TR₁ TS₂ τ _ _ r₁ r₂ w.hom
    apply NatTrans.ext
    funext A
    have hb : TS₂.map (eps.hom.app A.obj) ≫
        beta.hom.app (DerivedCategory.Q.obj (LC.obj A.obj)) =
        b.functor.map (Prod.mkHom (eps.hom.app Q.obj) (eps.hom.app A.obj)) := by
      change b.functor.map (Prod.mkHom (𝟙 _) _) ≫
        b.functor.map (Prod.mkHom _ (𝟙 _)) = _
      rw [← b.functor.map_comp]
      congr 1
      ext <;> simp
    have hn := representative_square o a b mu t Q.obj A.obj Q.property A.property
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.curry_obj_obj_obj,
      representativeSecond, Functor.isoWhiskerRight_trans, Iso.trans_assoc, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, fixedSecond, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.mapIso_hom, Iso.app_hom, Category.assoc, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, CategoryTheory.Functor.map_id,
      NatIso.ofComponents_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.curry_obj_obj_map, Bifunctor.map_id, Functor.curry_obj_map_app, Category.comp_id,
      Category.id_comp, reindexIso_hom_app, i, TR₀, j, TS₄, q, TR₁, r₁, rR, TS₂, τ, r₂, ee, eps,
      beta, w, TS₀, w₁, chi, c, w₂, s, rS, Q', w₀]
    erw [Category.id_comp, Category.id_comp, hb]
    exact hn
  exact NatTrans.CommShift.of_whiskerLeft τ q
    (fun X ↦ ⟨q.objPreimage X, (q.objObjPreimageIso X).inv, inferInstance⟩)

private theorem fixedFirst_global (o : Operation F R S)
    (a : TensorModel R) (b : TensorModel S) [sa : TensorShifts a] [sb : TensorShifts b]
    (mu : o.OrdinaryTensor) (t : TensorComparison o.pullback o.leftModel a b mu.iso)
    (N : Der R) : NatTrans.CommShift
      (fixedFirst a.functor b.functor o.left t.comparison.hom N) ℤ := by
  let := resolving_essSurj (R := R)
  let q := (resolving R).ι ⋙ DerivedCategory.Q
  let A := q.objPreimage N
  let e := q.objObjPreimageIso N
  have : NatTrans.CommShift
      (fixedFirst a.functor b.functor o.left t.comparison.hom (q.obj A)) ℤ :=
    fixedFirst_resolving o a b mu t A
  let e₁ := Functor.isoWhiskerRight ((Functor.curry.obj a.functor).flip.mapIso e) o.left
  let e₂ := Functor.isoWhiskerLeft o.left
    ((Functor.curry.obj b.functor).flip.mapIso (o.left.mapIso e))
  have : NatTrans.CommShift e₁.hom ℤ := by dsimp [e₁]; infer_instance
  have : NatTrans.CommShift e₂.hom ℤ := by dsimp [e₂]; infer_instance
  have ht : fixedFirst a.functor b.functor o.left t.comparison.hom N =
      e₁.inv ≫ fixedFirst a.functor b.functor o.left t.comparison.hom (q.obj A) ≫
        e₂.hom := by
    apply (cancel_epi e₁.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    apply NatTrans.ext
    funext M
    exact (fixedSecond a.functor b.functor o.left t.comparison.hom M).naturality e.hom
  rw [ht]
  infer_instance

private theorem fixedSecond_global (o : Operation F R S)
    (a : TensorModel R) (b : TensorModel S) [sa : TensorShifts a] [sb : TensorShifts b]
    (mu : o.OrdinaryTensor) (t : TensorComparison o.pullback o.leftModel a b mu.iso)
    (M : Der R) : NatTrans.CommShift
      (fixedSecond a.functor b.functor o.left t.comparison.hom M) ℤ := by
  let := resolving_essSurj (R := R)
  let q := (resolving R).ι ⋙ DerivedCategory.Q
  let A := q.objPreimage M
  let e := q.objObjPreimageIso M
  have : NatTrans.CommShift
      (fixedSecond a.functor b.functor o.left t.comparison.hom (q.obj A)) ℤ :=
    fixedSecond_resolving o a b mu t A
  let e₁ := Functor.isoWhiskerRight ((Functor.curry.obj a.functor).mapIso e) o.left
  let e₂ := Functor.isoWhiskerLeft o.left
    ((Functor.curry.obj b.functor).mapIso (o.left.mapIso e))
  have : NatTrans.CommShift e₁.hom ℤ := by dsimp [e₁]; infer_instance
  have : NatTrans.CommShift e₂.hom ℤ := by dsimp [e₂]; infer_instance
  have ht : fixedSecond a.functor b.functor o.left t.comparison.hom M =
      e₁.inv ≫ fixedSecond a.functor b.functor o.left t.comparison.hom (q.obj A) ≫
        e₂.hom := by
    apply (cancel_epi e₁.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    apply NatTrans.ext
    funext N
    exact (fixedFirst a.functor b.functor o.left t.comparison.hom N).naturality e.hom
  rw [ht]
  infer_instance

/-- A tensor comparison already normalized on resolving pairs respects both tensor shifts. -/
theorem tensorComparison_shifts
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}}
    {S : Sheaf K CommRingCat.{u + 1}}
    (o : Operation F R S) (a : TensorModel R) (b : TensorModel S)
    (sa : TensorShifts a) (sb : TensorShifts b) (mu : o.OrdinaryTensor)
    (t : TensorComparison o.pullback o.leftModel a b mu.iso) :
    TensorComparisonShifts t (sa := sa) (sb := sb) (sd := inferInstance) := by
  -- Use essential surjectivity instead of rigidity, and the existing general
  -- total-bifunctor comparison shift instances instead of repeating the sign calculation.
  let := sa
  let := sb
  constructor
  · intro M N n
    have := fixedFirst_global o a b mu t N
    convert (NatTrans.shift_app_comm
      (fixedFirst a.functor b.functor o.left t.comparison.hom N) n M).symm using 1 <;>
      simp only [Functor.commShiftIso_comp_hom_app, fixedFirst, Functor.comp_obj,
        Functor.flip_obj_map, Functor.curry_obj_map_app, Category.assoc]
    all_goals rfl
  · intro M N n
    have := fixedSecond_global o a b mu t M
    convert (NatTrans.shift_app_comm
      (fixedSecond a.functor b.functor o.left t.comparison.hom M) n N).symm using 1 <;>
      simp only [Functor.commShiftIso_comp_hom_app, fixedSecond, Functor.comp_obj,
        Functor.curry_obj_obj_map, Category.assoc]
    all_goals rfl

end AlgebraicGeometry.Scheme.ProjectionRestriction
