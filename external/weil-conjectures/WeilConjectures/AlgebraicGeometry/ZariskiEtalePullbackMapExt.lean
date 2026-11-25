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
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Identification of normalized pullback with exact-functor transport

Source: Stacks Project, Derived Categories, Tag 015B (4).
(blueprint: lem-weil-pbc-zariski-etale-pullback-map-ext)
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

set_option backward.isDefEq.respectTransparency false in
/-- The characterized object-cohomology pullback is exact-functor transport of Ext,
precomposed with a free-representable map whose generator is the adjunction unit.

Source: Stacks Project, Derived Categories, Tag 015B (4), lemma-higher-derived-functors;
Cohomology on Sites, Tag 0730; Homology, Tag 010T.
(blueprint: lem-weil-pbc-zariski-etale-pullback-map-ext)

Proof: For the fixed open V and map t, precomposition by Ext.mk₀ t after exact-functor
transport defines an additive family on Ext. Exact-functor transport preserves Yoneda
products and the extension class of a short exact sequence, hence this family commutes
with the displayed connecting maps. In degree zero naturality of the adjunction unit
and of evaluation of the identity generator identify it with the specified fstar.
For positive degree embed A into an injective B and form 0 → A → B → C → 0.
Ext(P(V), B, p+1) vanishes, so every class of degree p+1 is a connecting image
of a degree p class for C. Both families commute with that connecting map.
Induction on degree proves equality on every class. This also treats zero sheaves
and empty opens; degree zero uses no incoming differential. -/
theorem zariski_etale_pullback_eq_mapExt
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
    [PreservesFiniteColimits (sheafPullback i AddCommGrpCat.{u + 1}
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
    (V : X.Opens)
    (t : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free) ⟶
        (sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj
            ((presheafToSheaf (Opens.grothendieckTopology X.carrier)
              AddCommGrpCat.{u + 1}).obj (yoneda.obj V ⋙ AddCommGrpCat.free)))
    (ht : ((t.hom.app (op (i.obj V))).hom
        (((toSheafify X.smallEtaleTopology
          (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
            (FreeAbelianGroup.of (𝟙 (i.obj V))))) =
      ((((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).unit.app
          ((presheafToSheaf (Opens.grothendieckTopology X.carrier)
            AddCommGrpCat.{u + 1}).obj (yoneda.obj V ⋙ AddCommGrpCat.free))).hom.app
              (op V)).hom
        (((toSheafify (Opens.grothendieckTopology X.carrier)
          (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
            (FreeAbelianGroup.of (𝟙 V)))))
    (p : ℕ) (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})
    (x : Sheaf.H' A p V) :
    (fstar p V A).hom x = (Abelian.Ext.mk₀ t).comp
      (x.mapExactFunctor (sheafPullback i AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)) (zero_add p) := by
  classical
  let J := Opens.grothendieckTopology X.carrier
  let K := X.smallEtaleTopology
  let L := sheafPullback i AddCommGrpCat.{u + 1} J K
  let G := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K
  let adj := sheafAdjunctionContinuous i AddCommGrpCat.{u + 1} J K
  let P := (presheafToSheaf J AddCommGrpCat.{u + 1}).obj
    (yoneda.obj V ⋙ AddCommGrpCat.free)
  induction p generalizing A with
  | zero =>
    apply Abelian.Ext.addEquiv₀.injective
    apply (resolutionSectionEquiv K (i.obj V) (L.obj A)).injective
    have hzero := hfstar.2.2 V A x
    change resolutionSectionEquiv K (i.obj V) (L.obj A)
        (Abelian.Ext.addEquiv₀ ((fstar 0 V A).hom x)) =
      resolutionSectionEquiv J V (G.obj (L.obj A))
        ((Abelian.Ext.addEquiv₀ x) ≫ adj.unit.app A) at hzero
    refine hzero.trans ?_
    have hn : (Abelian.Ext.addEquiv₀ x) ≫ adj.unit.app A =
        adj.unit.app P ≫ G.map (L.map (Abelian.Ext.addEquiv₀ x)) :=
      adj.unit.naturality (Abelian.Ext.addEquiv₀ x)
    have ht' : resolutionSectionEquiv K (i.obj V) (L.obj P) t =
        resolutionSectionEquiv J V (G.obj (L.obj P)) (adj.unit.app P) := ht
    have hm : (Abelian.Ext.mk₀ t).comp (x.mapExactFunctor L) (zero_add 0) =
        Abelian.Ext.mk₀ (t ≫ L.map (Abelian.Ext.addEquiv₀ x)) := by
      conv_lhs => rw [← Abelian.Ext.mk₀_addEquiv₀_apply x]
      rw [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
      rfl
    rw [hm]
    have hm0 : Abelian.Ext.addEquiv₀
        (Abelian.Ext.mk₀ (t ≫ L.map (Abelian.Ext.addEquiv₀ x))) =
      t ≫ L.map (Abelian.Ext.addEquiv₀ x) :=
        Abelian.Ext.addEquiv₀.apply_symm_apply _
    refine Eq.trans ?_ (congrArg (resolutionSectionEquiv K (i.obj V) (L.obj A)) hm0.symm)
    refine (congrArg (resolutionSectionEquiv J V (G.obj (L.obj A))) hn).trans ?_
    exact congrArg
      (fun z ↦ (L.map (Abelian.Ext.addEquiv₀ x)).hom.app (op (i.obj V)) z) ht'.symm
  | succ p ih =>
    let S : ShortComplex (Sheaf J AddCommGrpCat.{u + 1}) :=
      ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A))
        (cokernel.condition (Injective.ι A))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel (Injective.ι A) }
    have hS' := hS.map_of_exact L
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ P hS x
      (Abelian.Ext.eq_zero_of_injective _) rfl
    rw [← hy, hfstar.2.1 S hS hS' p V y, ih]
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
    rw [Abelian.Ext.comp_assoc]
    omega
