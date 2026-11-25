/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Evaluation components with a fixed normalized tensor comparison

Source: Stacks Project, Tag 0A8X, ordinary tensor totalization; the open-site
reindexing construction in Mathlib `Scheme.Modules.overEquiv`.
(blueprint: lem-pc-ordinary-evaluation-component-over-transport). -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

private theorem ordinaryEvaluation_transport_composition
    {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {A B E H : C} {A' B' E' H' V : D}
    (μ : A' ≅ L.obj A) (c : L.obj B ≅ B') (b : L.obj E ≅ E') (e : L.obj H ≅ H')
    (i : A ⟶ B) (f : B ⟶ E) (π : E ⟶ H)
    (j : A' ⟶ B') (q : E' ⟶ H') (t : V ⟶ A')
    (hc : L.map i ≫ c.hom = μ.inv ≫ j)
    (hπ : b.hom ≫ q = L.map π ≫ e.hom) :
    t ≫ j ≫ c.inv ≫ L.map f ≫ b.hom ≫ q =
      t ≫ μ.hom ≫ L.map (i ≫ f ≫ π) ≫ e.hom := by
  have hi : j ≫ c.inv = μ.hom ≫ L.map i := by
    apply (cancel_mono c.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hc,
      Iso.hom_inv_id_assoc]
  rw [reassoc_of% hi, hπ]
  simp only [Functor.map_comp, Category.assoc]

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

noncomputable local instance ordinarySummandProjectionOverPreadditive
    (X : Scheme.{u}) (U : X.Opens) :
    MonoidalPreadditive (localEvaluationModules X U) :=
  Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1

noncomputable local instance ordinarySummandProjectionSchemePreadditive (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1

attribute [local irreducible] homComplexFunctor Scheme.Modules.overEquiv
  Scheme.Modules.overEquivFunctorObjUnitIso HomologicalComplex.singleMapHomologicalComplex

set_option linter.unusedVariables false in
/-- Transport of one tensor summand followed by one Hom projection.
Source: Stacks Project, Tag 0A8X, total tensor and Hom-complex projections.
(blueprint: lem-pc-ordinary-evaluation-transport-summand-projection).

Proof: apply naturality of the total tensor map for the inverse of `d` to
move the tensor summand across that map. The summand equation for `c`,
postcomposed with its inverse, moves it across `c.inv`. The projection
equation for `b F` moves the final projection to the image of the local
projection. Functoriality combines the three local arrows. This calculation
is valid for every `f` and does not use an evaluation formula. -/
theorem ordinaryEvaluation_transport_summand_projection (X : Scheme.{u}) (U : X.Opens)
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
    ∀ (d : T.obj (localEvaluationDual X U P) ≅
        homComplex (R := U.toScheme.sheaf) (T.obj P)
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))))
      (m : L.CoreMonoidal)
      (F : CochainComplex (localEvaluationModules X U) ℤ)
      (c : T.obj (localEvaluationTensor X U P F) ≅
        pullbackTensorTotal U.toScheme (T.obj F) (T.obj (localEvaluationDual X U P)))
      (_hc : ∀ (p q n : ℤ) (h : p + q = n),
        L.map (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
            (curriedTensor _) (.up ℤ) p q n h) ≫ c.hom.f n =
          (m.μIso (F.X p) ((localEvaluationDual X U P).X q)).inv ≫
            HomologicalComplex.ιMapBifunctor (T.obj F) (T.obj (localEvaluationDual X U P))
              (curriedTensor _) (.up ℤ) p q n h)
      (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
      (p q n r : ℤ) (hpq : p + q = n),
      letI := SheafOfModules.monoidalCategory U.toScheme.sheaf
      letI := SheafOfModules.symmetricCategory U.toScheme.sheaf
      let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
      let D := homComplex (R := U.toScheme.sheaf) (T.obj P) O
      let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := U.toScheme.sheaf))
      HomologicalComplex.ιMapBifunctor (T.obj F) D (curriedTensor _)
          (.up ℤ) p q n hpq ≫
        ((c ≪≫ (((curriedTensor (SheafOfModules.{u}
          (moduleRings U.toScheme.toRingedSpace))).map₂CochainComplex).obj
            (T.obj F)).mapIso d).inv ≫ T.map f ≫ (b F).hom).f n ≫
        π (T.obj P) (T.obj F) n r (r + n) rfl =
      (𝟙 ((T.obj F).X p) ⊗ₘ d.inv.f q) ≫
        (m.μIso (F.X p) ((localEvaluationDual X U P).X q)).hom ≫
        L.map (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
          (curriedTensor _) (.up ℤ) p q n hpq ≫ f.f n ≫
          localEvaluationProjection X U P F n r (r + n) rfl) ≫
        (e (P.X r) (F.X (r + n))).hom  := by
  intro L T e b hπ d m F c hc f p q n r hpq O D π
  simp only [HomologicalComplex.comp_f, Iso.trans_inv, Functor.mapIso_inv,
    Category.assoc]
  dsimp only [Functor.map₂CochainComplex, Functor.map₂HomologicalComplex]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f]
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    simp only [curriedTensor_map_app, curriedTensor_obj_map, id_whiskerRight,
      Category.id_comp, tensorHom_def]
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      exact ordinaryEvaluation_transport_composition L
        (m.μIso (F.X p) ((localEvaluationDual X U P).X q))
        ((HomologicalComplex.eval _ (.up ℤ) n).mapIso c)
        ((HomologicalComplex.eval _ (.up ℤ) n).mapIso (b F))
        (e (P.X r) (F.X (r + n))) _ (f.f n)
        (localEvaluationProjection X U P F n r (r + n) rfl) _ _ _
        (hc p q n hpq) (hπ F n r (r + n) rfl)

end AlgebraicGeometry
