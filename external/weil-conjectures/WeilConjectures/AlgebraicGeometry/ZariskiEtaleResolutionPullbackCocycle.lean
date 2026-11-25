/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.AlgebraicGeometry.ZariskiEtalePullbackMapExt
import WeilConjectures.CategoryTheory.ExactFunctorResolutionCocycle


/-! # Cocycle comparisons for object cohomology

Source: Stacks Project, Cohomology, Tags 01F8 and 01FB;
Derived Categories, Tags 013P and 015B (4).
(blueprint: lem-weil-pbc-zariski-etale-resolution-pullback-cocycle)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

private noncomputable def resolutionSectionEquiv
    {C : Type*} [Category.{u + 1} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (V : C)
    (A : Sheaf J AddCommGrpCat.{u + 1}) :
    ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ A) ≃ A.obj.obj (op V) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ A).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj V) A.obj).trans yonedaEquiv)

/-- The characterized pullback-counit map sends a resolution cocycle to the
section cocycle obtained by an augmented comparison.

Source: Stacks Project, Cohomology, Tag 01FB; Derived Categories, Tags 013P
and 015B (4); Cohomology on Sites, Section 01FT and Tag 0730.
(blueprint: lem-weil-pbc-zariski-etale-resolution-pullback-cocycle)

Proof: Construct t from the adjunction-unit section using the inverse of the
sheafification, free-abelian and Yoneda adjunction equivalences. In degree zero,
unit naturality identifies pullback with precomposition by t after exact-functor
transport of Ext. In positive degree, embed the coefficient sheaf into an
injective and use the surjective connecting map from its cokernel. Induction
and the assumed boundary compatibility identify this family with fstar; this
is zariski_etale_pullback_eq_mapExt.
Transpose each component of the supplied b through the inverse-image/direct-image
adjunction to obtain e : LR → I. Adjunction naturality gives the chain-map
equations, and hb gives the counit augmentation. Naturality of the unit and
evaluation of t show that t followed by L(a) followed by e evaluates to the
section prescribed by hsec. The free-representable section equivalence is
injective, so this composite equals c. The theorem
exactFunctor_resolution_cocycle computes exact-functor transport followed by
the counit using e. Reassociate the Ext products and use
InjectiveResolution.mk₀_comp_extMk to precompose the cocycle with t. Substitute
the equality with c to finish. No injective preservation by inverse image,
homology equivalence, or choice of an arbitrary existence witness is used.
Degree zero and zero sheaves require no additional hypotheses. -/
theorem zariski_etale_resolution_pullback_cocycle
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)]
    (fstar : ∀ (p : ℕ) (V : X.Opens)
      (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}),
      Sheaf.H' A p V ⟶
        Sheaf.H' ((sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj A)
          p (i.obj V))
    (hfstar : (∀ (p : ℕ) (V : X.Opens) (A A' : Sheaf (Opens.grothendieckTopology X.carrier)
      AddCommGrpCat.{u + 1}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p).map φ).app
          (op V) ≫
            fstar p V A' =
          fstar p V A ≫
            ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology p).map
              ((sheafPullback i AddCommGrpCat.{u + 1}
                (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map φ)).app
                  (op (i.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}))
        (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)).ShortExact)
        (p : ℕ) (V : X.Opens) (x : Sheaf.H' S.X₃ p V),
        (fstar (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fstar p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : X.Opens) (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})
        (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fstar 0 V A).hom x)).hom.app (op (i.obj V))).hom
            (((toSheafify X.smallEtaleTopology
              (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (i.obj V)))) =
          (((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).unit.app A).hom.app
              (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify (Opens.grothendieckTopology X.carrier)
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V))))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F)
    (R : InjectiveResolution ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F))
    (b : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
    (hb : R.ι.f 0 ≫ b.f 0 = (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map (I.ι.f 0))
    (q : ℕ) (V : X.Opens)
    (a : (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}).obj
        (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ R.cocomplex.X q)
    (ha : a ≫ R.cocomplex.d q (q + 1) = 0)
    (c : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X q)
    (hc : c ≫ I.cocomplex.d q (q + 1) = 0)
    (hsec : (b.f q).hom.app (op V) ((a.hom.app (op V)).hom
          (((toSheafify (Opens.grothendieckTopology X.carrier)
            (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
              (FreeAbelianGroup.of (𝟙 V)))) =
        ((c.hom.app (op (i.obj V))).hom
          (((toSheafify X.smallEtaleTopology
            (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
              (FreeAbelianGroup.of (𝟙 (i.obj V)))))) :
      (fstar q V
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) ≫
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology q).map
          ((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).counit.app F)).app
              (op (i.obj V))).hom (R.extMk a (q + 1) rfl ha) = I.extMk c (q + 1) rfl hc := by
  classical
  let J := Opens.grothendieckTopology X.carrier
  let K := X.smallEtaleTopology
  let L := sheafPullback i AddCommGrpCat.{u + 1} J K
  let G := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K
  let adj := sheafAdjunctionContinuous i AddCommGrpCat.{u + 1} J K
  let : PreservesColimits L := adj.leftAdjoint_preservesColimits
  let P := (presheafToSheaf J AddCommGrpCat.{u + 1}).obj
    (yoneda.obj V ⋙ AddCommGrpCat.free)
  let t := (resolutionSectionEquiv K (i.obj V) (L.obj P)).symm
    (resolutionSectionEquiv J V (G.obj (L.obj P)) (adj.unit.app P))
  have ht : resolutionSectionEquiv K (i.obj V) (L.obj P) t =
      resolutionSectionEquiv J V (G.obj (L.obj P)) (adj.unit.app P) :=
    Equiv.apply_symm_apply _ _
  let e : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex ⟶
      I.cocomplex :=
    { f := fun n ↦ (adj.homEquiv _ _).symm (b.f n)
      comm' := by
        intro n m _
        change (adj.homEquiv _ _).symm (b.f n) ≫ I.cocomplex.d n m =
          L.map (R.cocomplex.d n m) ≫ (adj.homEquiv _ _).symm (b.f m)
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simpa using (b.comm n m) }
  have he : L.map (R.ι.f 0) ≫ e.f 0 = adj.counit.app F ≫ I.ι.f 0 := by
    change L.map (R.ι.f 0) ≫ (adj.homEquiv _ _).symm (b.f 0) =
      adj.counit.app F ≫ I.ι.f 0
    rw [← adj.homEquiv_naturality_left_symm, hb]
    change (adj.homEquiv (G.obj F) (I.cocomplex.X 0)).symm (G.map (I.ι.f 0)) =
      adj.counit.app F ≫ I.ι.f 0
    have h := adj.homEquiv_naturality_right_symm (𝟙 (G.obj F)) (I.ι.f 0)
    have hε := adj.homEquiv_symm_id F
    change (adj.homEquiv (G.obj F) F).symm (𝟙 (G.obj F)) = adj.counit.app F at hε
    rw [hε] at h
    simpa only [Category.id_comp] using h
  have hca : (L.map a ≫ e.f q) ≫ I.cocomplex.d q (q + 1) = 0 := by
    have hecomm := e.comm q (q + 1)
    change e.f q ≫ I.cocomplex.d q (q + 1) =
      L.map (R.cocomplex.d q (q + 1)) ≫ e.f (q + 1) at hecomm
    rw [Category.assoc, hecomm]
    rw [← L.map_comp_assoc, ha, L.map_zero, zero_comp]
  have hte : t ≫ L.map a ≫ e.f q = c := by
    apply (resolutionSectionEquiv K (i.obj V) (I.cocomplex.X q)).injective
    have hcompK (A B : Sheaf K AddCommGrpCat.{u + 1})
        (u : (presheafToSheaf K AddCommGrpCat.{u + 1}).obj
          (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free) ⟶ A) (f : A ⟶ B) :
        resolutionSectionEquiv K (i.obj V) B (u ≫ f) =
          (f.hom.app (op (i.obj V))).hom
            (resolutionSectionEquiv K (i.obj V) A u) := by
      rfl
    have hcompJ (A B : Sheaf J AddCommGrpCat.{u + 1})
        (u : (presheafToSheaf J AddCommGrpCat.{u + 1}).obj
          (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ A) (f : A ⟶ B) :
        resolutionSectionEquiv J V B (u ≫ f) =
          (f.hom.app (op V)).hom (resolutionSectionEquiv J V A u) := by
      rfl
    have hn : a ≫ adj.unit.app (R.cocomplex.X q) =
        adj.unit.app P ≫ G.map (L.map a) := adj.unit.naturality a
    have hbe : adj.unit.app (R.cocomplex.X q) ≫ G.map (e.f q) = b.f q := by
      exact (adj.homEquiv _ _).apply_symm_apply (b.f q)
    have hn' : adj.unit.app P ≫ G.map (L.map a ≫ e.f q) = a ≫ b.f q := by
      rw [G.map_comp, ← Category.assoc, ← hn, Category.assoc, hbe]
    have hs := congrArg (resolutionSectionEquiv J V (G.obj (I.cocomplex.X q))) hn'
    rw [hcompJ, hcompJ] at hs
    rw [hcompK, ht]
    exact hs.trans hsec
  change (((Sheaf.cohomologyPresheafFunctor K q).map (adj.counit.app F)).app
    (op (i.obj V))).hom ((fstar q V (G.obj F)).hom (R.extMk a (q + 1) rfl ha)) = _
  rw [zariski_etale_pullback_eq_mapExt i hi fstar hfstar V t ht]
  change ((Abelian.Ext.mk₀ t).comp
    ((R.extMk a (q + 1) rfl ha).mapExactFunctor L) (zero_add q)).comp
      (Abelian.Ext.mk₀ (adj.counit.app F)) (add_zero q) = _
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [exactFunctor_resolution_cocycle L (adj.counit.app F) R I e he q a ha hca]
  rw [I.mk₀_comp_extMk]
  simp only [hte]
