/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The inverse open-site dual comparison on product projections

Source: Stacks Project, Tags 0A8X and 08DL; Hom-complex product projections.
(blueprint: lem-pc-ordinary-evaluation-over-dual-projection). -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

noncomputable local instance ordinaryDualProjectionOverPreadditive
    (X : Scheme.{u}) (U : X.Opens) :
    MonoidalPreadditive (localEvaluationModules X U) :=
  Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1

noncomputable local instance ordinaryDualProjectionSchemePreadditive (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1

private theorem dualProjection_id_first
    {C D E : Type*} [Category C] [Category D] [Category E]
    (G : Cᵒᵖ ⥤ D ⥤ E) (A : C) {M N : D} (f : M ⟶ N) :
    (G.map (𝟙 A).op).app M ≫ (G.obj (op A)).map f = (G.obj (op A)).map f := by
  rw [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

private theorem dualProjection_comp_transport
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E : C} {H K N V W : D}
    (p : A ⟶ B) (s : B ⟶ E)
    (b : F.obj A ⟶ H) (a : H ⟶ K) (π : H ⟶ N) (π' : K ⟶ V)
    (e : F.obj B ⟶ N) (e' : F.obj E ⟶ W)
    (f : N ⟶ V) (t : V ⟶ W) (g : N ⟶ W)
    (hb : b ≫ π = F.map p ≫ e) (ha : a ≫ π' = π ≫ f)
    (he : F.map s ≫ e' = e ≫ g) (hf : f ≫ t = g) :
    (b ≫ a) ≫ π' ≫ t = F.map (p ≫ s) ≫ e' := by
  rw [Category.assoc, ← Category.assoc a, ha, Category.assoc π, hf,
    ← Category.assoc, hb, Category.assoc, ← he, ← Category.assoc, ← F.map_comp]

attribute [local irreducible] homComplexFunctor Scheme.Modules.overEquiv
  Scheme.Modules.overEquivFunctorObjUnitIso HomologicalComplex.singleMapHomologicalComplex

set_option linter.unusedVariables false in
/-- The inverse transported dual comparison recovers the unit-valued projection.
Source: Stacks Project, Tags 0A8X and 08DL, product projections and open restriction.
(blueprint: lem-pc-ordinary-evaluation-over-dual-projection).

Proof: apply the functorial projection equation of homComplex_projections_exists
with identity in the first variable and a.hom in the second variable. Compose
on the left with the hom of b at the single unit. Its projection is hπ.
Use naturality he for the singleObjXSelf map to move that output map across e.
The degree-zero component of a, followed by singleObjXSelf on the scheme,
is L(singleObjXSelf) followed by the inverse normalized unit isomorphism:
expand the two factors of a, use singleMapHomologicalComplex_hom_app_self
and single_map_f_self, and cancel singleObjXSelf with its inverse.
Functoriality of homObjMap then identifies the resulting equation with
d.hom.f q followed by the scheme unit-valued projection. Precompose with
d.inv.f q and cancel using the degree-q component of d.inv_hom_id.
This proves the displayed equation, without any tensorator or complex F.
Empty opens and zero complexes require no separate assumptions. -/
theorem ordinaryEvaluation_over_dual_projection (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∀ (e : ∀ A B : localEvaluationModules X U,
      L.obj
          (SheafOfModules.homObj (R := X.sheaf.over U) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.sheaf)
          (L.obj A)
          (L.obj B))
    (he : ∀ (A A' B B' : localEvaluationModules X U) (f : A' ⟶ A) (g : B ⟶ B'),
      L.map
          (SheafOfModules.homObjMap (R := X.sheaf.over U) f g) ≫
          (e A' B').hom =
        (e A B).hom ≫ SheafOfModules.homObjMap (R := U.toScheme.sheaf)
          (L.map f)
          (L.map g))
    (b : ∀ M : CochainComplex (localEvaluationModules X U) ℤ,
      T.obj
          (homComplex (R := X.sheaf.over U) P M) ≅
        homComplex (R := U.toScheme.sheaf)
          (T.obj P)
          (T.obj M))
    (hπ : ∀ (M : CochainComplex (localEvaluationModules X U) ℤ)
          (n r s : ℤ) (h : r + n = s),
        (b M).hom.f n ≫
            (Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := U.toScheme.sheaf)))
              (T.obj P)
              (T.obj M)
              n r s h =
          L.map
            (localEvaluationProjection X U P M n r s h) ≫
            (e (P.X r) (M.X s)).hom),
    let a : T.obj (localEvaluationUnit X U) ≅
        (HomologicalComplex.single _ (.up ℤ) 0).obj
          (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) :=
      by
        set_option backward.isDefEq.respectTransparency true in
          exact (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app _ ≪≫
            (HomologicalComplex.single _ (.up ℤ) 0).mapIso
              (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
    let d := b (localEvaluationUnit X U) ≪≫
      ((homComplexFunctor.{u, u, u, u} (R := U.toScheme.sheaf)).obj (op (T.obj P))).mapIso a
    ∀ (q r : ℤ) (h : r + q = 0),
      d.inv.f q ≫
        L.map (localEvaluationProjection X U P (localEvaluationUnit X U) q r 0 h ≫
          SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0
              (𝟙_ (localEvaluationModules X U))).hom) ≫
        (e (P.X r) (𝟙_ (localEvaluationModules X U))).hom ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf) (𝟙 (L.obj (P.X r)))
          (Scheme.Modules.overEquivFunctorObjUnitIso U).inv =
      (Classical.choose (homComplex_projections_exists.{u, u, u, u}
        (R := U.toScheme.sheaf))) (T.obj P)
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))) q r 0 h ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf) (𝟙 ((T.obj P).X r))
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))).hom := by
  classical
  intro L T e he b hπ a d q r h
  let π := Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (R := U.toScheme.sheaf))
  let M := localEvaluationUnit X U
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
  let s := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (𝟙_ (localEvaluationModules X U))
  let t := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
  let z := Scheme.Modules.overEquivFunctorObjUnitIso U
  have ha : a.hom.f 0 ≫ t.hom = L.map s.hom ≫ z.inv := by
    dsimp only [a, t, s, z, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      HomologicalComplex.comp_f, Iso.app_hom]
    simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := U.toScheme.sheaf))).2.2
      (T.obj P) (T.obj P) (T.obj M) O (𝟙 (T.obj P)) a.hom q r 0 h
  have hf := dualProjection_id_first
    (homComplexFunctor.{u, u, u, u} (R := U.toScheme.sheaf)) (T.obj P) a.hom
  have hn' := (congrArg (fun f ↦ f.f q ≫ π (T.obj P) O q r 0 h) hf).symm.trans hn
  change
    (((homComplexFunctor (R := U.toScheme.sheaf)).obj (op (T.obj P))).map a.hom).f q ≫
      π (T.obj P) O q r 0 h =
      π (T.obj P) (T.obj M) q r 0 h ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf) (𝟙 ((T.obj P).X r))
          (a.hom.f 0) at hn'
  have hd : d.hom.f q ≫ π (T.obj P) O q r 0 h ≫
      SheafOfModules.homObjMap (R := U.toScheme.sheaf) (𝟙 ((T.obj P).X r)) t.hom =
    L.map (localEvaluationProjection X U P M q r 0 h ≫
      SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r)) s.hom) ≫
      (e (P.X r) (𝟙_ (localEvaluationModules X U))).hom ≫
      SheafOfModules.homObjMap (R := U.toScheme.sheaf) (𝟙 (L.obj (P.X r))) z.inv := by
    change ((b M).hom.f q ≫
      (((homComplexFunctor (R := U.toScheme.sheaf)).obj (op (T.obj P))).map a.hom).f q) ≫
        π (T.obj P) O q r 0 h ≫ _ = _
    refine dualProjection_comp_transport L
      (localEvaluationProjection X U P M q r 0 h)
      (SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r)) s.hom)
      _ _ _ _ _ _ _ _
      (SheafOfModules.homObjMap (R := U.toScheme.sheaf) (L.map (𝟙 (P.X r)))
        (L.map s.hom) ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf) (𝟙 (L.obj (P.X r))) z.inv)
      (hπ M q r 0 h) hn' ?_ ?_
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f ↦ f ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf) (𝟙 (L.obj (P.X r))) z.inv)
        (he _ _ _ _ (𝟙 (P.X r)) s.hom)).trans (Category.assoc _ _ _))
    · simp only [SheafOfModules.homObjMap_comp_homObjMap,
        CategoryTheory.Functor.map_id, Category.id_comp, ha]
      rfl
  exact (Iso.inv_comp_eq ((HomologicalComplex.eval _ _ q).mapIso d)).2 hd.symm


end AlgebraicGeometry
