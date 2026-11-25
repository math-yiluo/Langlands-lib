/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
import WeilConjectures.Algebra.Homology.ShortComplex.MapHomologyIsoComp
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Normalized cohomology comparisons for exact derived functors

Source: Stacks Project, Tag 015F, `lemma-right-derived-exact-functor`, with the
kernel/quotient and localization coherence argument in the DAG node
(blueprint: lem-pur-exact-derived-cohomology-coherence).

The comparisons are the existing `Functor.mapDerivedCategoryHomologyFunctorIso`, not
arbitrary isomorphisms. Their normalization on representatives is
`Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q`: the inverse complex homology
comparison, transported through `homologyFunctorFactors` and `mapDerivedCategoryFactors`.
Being natural isomorphisms on the entire derived category, they are natural for all
derived morphisms and independent of representatives.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA wA uB vB wB uC vC wC

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized cohomology comparisons for exact functors respect the termwise
compositor and every natural isomorphism from the composite to another exact functor.
Source: Stacks Project, Tag 015F, `lemma-right-derived-exact-functor`; the canonical
coherence strengthening (blueprint: lem-pur-exact-derived-cohomology-coherence).

Here theta is `mapDerivedCategoryHomologyFunctorIso`, c is `mapDerivedCategoryCompIso`,
and d is c inverse followed by `mapDerivedCategoryNatIso eta`. These existing constructions
use ordinary unbounded derived categories. The representative formula for theta is
`mapDerivedCategoryHomologyFunctorIso_hom_app_Q`.

Proof plan, following the node's seven steps:
1. Exactness preserves kernels, images and quotients by
   `lem-sp-exact-functor-preserves-homology`. Inverting its homology comparison gives
   t, characterized by t F(p) = p z on cycles and their homology quotient. Its naturality
   also shows that the termwise functor preserves quasi-isomorphisms in every degree.
2. Lift t through the complex localization using clause (2) of
   `lem-weil-pbc-localization-universal-property`. Transport by the cohomology and
   termwise-functor factorizations gives exactly the existing theta. Uniqueness makes
   it natural for all derived morphisms, independently of the representative.
3. The two cycle maps for GF agree after the kernel inclusion, so cancel that mono.
   Compose with the homology quotient and cancel the preserved epi GF(p); this proves
   t_GF = t_G G(t_F) on complexes.
4. The termwise identity lifts to c with its normalization `mapDerivedCategoryCompIso_fac`.
   Substitute the representative formula of step 2 and use naturality of theta_G.
   Cancel the factorization isomorphisms, apply step 3, and descend equality using
   clause (3) of `lem-weil-pbc-localization-universal-property`.
5. For eta, naturality on the cycle inclusion and its monicity give compatibility of
   cycle maps. Naturality on the homology quotient and its preserved epicity then give
   H(eta) t_GF = t_L eta_H on complexes.
6. Lift eta by clause (2) of the localization property. Substitute step 2, cancel the
   functor factorizations, and use naturality of the cohomology factorizations and eta.
   Step 5 and clause (3) give H(D eta) theta_GF = theta_L eta_H on the derived category.
7. Substitute step 4 into the second asserted equation. Since d = c inverse followed
   by D eta, functoriality of cohomology cancels c with its inverse and step 6 finishes.
   Only three consecutive complex terms and the unbounded localization were used;
   neither boundedness nor a resolution is required.
-/
theorem exactDerivedCohomologyCoherence
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : ℤ) :
    (∀ K : DerivedCategory A,
      (@mapDerivedCategoryHomologyFunctorIso A C _ _ _ _ _ _ (F ⋙ G) _
        (comp_preservesFiniteLimits F G) (comp_preservesFiniteColimits F G) a).hom.app K ≫
          (DerivedCategory.homologyFunctor C a).map
            ((mapDerivedCategoryCompIso F G).inv.app K) =
        G.map ((F.mapDerivedCategoryHomologyFunctorIso a).hom.app K) ≫
          (G.mapDerivedCategoryHomologyFunctorIso a).hom.app (F.mapDerivedCategory.obj K)) ∧
    (∀ (L : A ⥤ C) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
      (eta : F ⋙ G ≅ L) (K : DerivedCategory A),
      G.map ((F.mapDerivedCategoryHomologyFunctorIso a).hom.app K) ≫
          (G.mapDerivedCategoryHomologyFunctorIso a).hom.app (F.mapDerivedCategory.obj K) ≫
          (DerivedCategory.homologyFunctor C a).map
            ((mapDerivedCategoryCompIso F G ≪≫
              @mapDerivedCategoryNatIso A C _ _ _ _ _ _ (F ⋙ G) L _ _
                (comp_preservesFiniteLimits F G) (comp_preservesFiniteColimits F G)
                _ _ eta).hom.app K) =
        eta.hom.app ((DerivedCategory.homologyFunctor A a).obj K) ≫
          (L.mapDerivedCategoryHomologyFunctorIso a).hom.app K) := by
  let := comp_preservesFiniteLimits F G
  let := comp_preservesFiniteColimits F G
  have hcomplex (X : CochainComplex A ℤ) :
      ((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app X =
        G.map ((F.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app X) ≫
          (G.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app
            ((F.mapHomologicalComplex (.up ℤ)).obj X) := by
    have he (H : A ⥤ C) [H.Additive] [H.PreservesHomology] :
        (H.mapHomologicalComplexHomologyIso (.up ℤ) a).app X =
          (X.sc a).mapHomologyIso H :=
      Iso.ext (mapHomologicalComplexHomologyIso_hom_app_eq _ _ _ _)
    have heF : (F.mapHomologicalComplexHomologyIso (.up ℤ) a).app X =
        (X.sc a).mapHomologyIso F :=
      Iso.ext (mapHomologicalComplexHomologyIso_hom_app_eq _ _ _ _)
    have heG : (G.mapHomologicalComplexHomologyIso (.up ℤ) a).app
        ((F.mapHomologicalComplex (.up ℤ)).obj X) =
          ((X.sc a).map F).mapHomologyIso G :=
      Iso.ext (mapHomologicalComplexHomologyIso_hom_app_eq _ _ _ _)
    simp only [← Iso.app_inv, he, heF, heG, ShortComplex.mapHomologyIso_comp,
      Iso.trans_inv, Functor.mapIso_inv]
  have hcomp :
      ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso a).hom ≫
          whiskerRight (mapDerivedCategoryCompIso F G).inv
            (DerivedCategory.homologyFunctor C a) =
        whiskerRight (F.mapDerivedCategoryHomologyFunctorIso a).hom G ≫
          whiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyFunctorIso a).hom := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) (fun X ↦ ?_)
    have hc : (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj X) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj X) =
        (F ⋙ G).mapDerivedCategoryFactors.hom.app X := by
      have h := mapDerivedCategoryCompIso_fac F G X
      have hid : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app X =
          𝟙 _ := rfl
      rw [hid] at h
      erw [DerivedCategory.Q.map_id, Category.comp_id] at h
      exact h
    have hfac : (F ⋙ G).mapDerivedCategoryFactors.inv.app X ≫
        (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj X) =
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
      apply (cancel_mono (G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app X) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj X))).1
      simp only [Category.assoc, hc, Iso.inv_hom_id_app]
      erw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
      erw [G.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]
      rfl
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
      mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp, hfac, Functor.map_comp]
    have hn := (G.mapDerivedCategoryHomologyFunctorIso a).hom.naturality
      (F.mapDerivedCategoryFactors.inv.app X)
    dsimp only [Functor.comp_map] at hn
    erw [hn]
    dsimp only [Functor.comp_obj]
    erw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Category.assoc]
    erw [← G.map_comp_assoc
      ((DerivedCategory.homologyFunctorFactors B a).inv.app _)
      ((DerivedCategory.homologyFunctorFactors B a).hom.app _),
      Iso.inv_hom_id_app, G.map_id, Category.id_comp]
    rw [hcomplex]
    simp only [Category.assoc]
    rfl
  refine ⟨fun K ↦ congr_app hcomp K, ?_⟩
  intro L _ _ _ eta K
  have hk := congr_app hcomp K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hk
  rw [← Category.assoc, ← hk]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  exact (mapDerivedCategoryHomologyFunctorIso_hom_app_naturality eta a K).symm

end CategoryTheory.Functor
