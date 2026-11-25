/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Comparison squares and direct-sum totalization -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

local notation "Tot[" F "]" => CategoryTheory.Functor.uncurry.obj
  (CategoryTheory.Functor.map₂HomologicalComplex F
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The uncurried total bifunctor sends a pair of maps to the totalized bifunctor map.
(blueprint: lem-pbc-tensor-total-comparison-square) -/
theorem mapTotalBifunctor {A : Type*} [Category* A] [Abelian A]
    [HasCoproducts.{0} A] (F : A ⥤ A ⥤ A)
    [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
    {Z W : CochainComplex A ℤ × CochainComplex A ℤ} (v : Z ⟶ W) :
    (Tot[F]).map v = mapBifunctorMap v.1 v.2 F (.up ℤ) := by
  simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex]
  simp [mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasCoproducts.{0} D]
  (C : A ⥤ B) (U : B ⥤ D) (I : A ⥤ D)
  [C.Additive] [U.Additive] [I.Additive] [U.IsEquivalence]
  (FA : A ⥤ A ⥤ A) (FB : B ⥤ B ⥤ B) (FD : D ⥤ D ⥤ D)
  [FA.PreservesZeroMorphisms] [∀ M, (FA.obj M).PreservesZeroMorphisms]
  [FB.PreservesZeroMorphisms] [∀ M, (FB.obj M).PreservesZeroMorphisms]
  [FD.PreservesZeroMorphisms] [∀ M, (FD.obj M).PreservesZeroMorphisms]

/-- An ordinary bifunctor square induces the corresponding square on total complexes.
Source: Stacks, Cohomology on Sites, Tag 07A4, signed direct-sum totalization.
(blueprint: lem-pbc-tensor-total-comparison-square)

Proof: cancel the two total-comparison isomorphisms. In each degree, U preserves
the coproduct since it is an equivalence. Test on every bidegree injection. The
summand formula for the first comparison and naturality of alpha reduce the left
side to the ordinary square. The summand formula for sigma, the formula for mapping
chain maps through a bifunctor, and the second comparison's summand formula give
exactly the same composite on the right. Degreewise extensionality finishes.
The argument works with zero objects and empty sums and requires no boundedness. -/
theorem tensorTotalComparisonSquare
    (alpha : C ⋙ U ≅ I)
    (alphaC : C.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      I.mapHomologicalComplex (.up ℤ))
    (halpha : ∀ (P : CochainComplex A ℤ) (n : ℤ),
      (alphaC.hom.app P).f n = alpha.hom.app (P.X n))
    (muC : ∀ M N : A,
      C.obj ((FA.obj M).obj N) ≅ (FB.obj (C.obj M)).obj (C.obj N))
    (muI : ∀ M N : A,
      I.obj ((FA.obj M).obj N) ≅ (FD.obj (I.obj M)).obj (I.obj N))
    (tC : ∀ P Q : CochainComplex A ℤ,
      (Tot[FB]).obj (((C.mapHomologicalComplex (.up ℤ)).obj P),
        ((C.mapHomologicalComplex (.up ℤ)).obj Q)) ≅
          (C.mapHomologicalComplex (.up ℤ)).obj ((Tot[FA]).obj (P, Q)))
    (tI : ∀ P Q : CochainComplex A ℤ,
      (Tot[FD]).obj (((I.mapHomologicalComplex (.up ℤ)).obj P),
        ((I.mapHomologicalComplex (.up ℤ)).obj Q)) ≅
          (I.mapHomologicalComplex (.up ℤ)).obj ((Tot[FA]).obj (P, Q)))
    (htC : ∀ (P Q : CochainComplex A ℤ) (a b n : ℤ) (h : a + b = n),
      CochainComplex.ιMapBifunctor ((C.mapHomologicalComplex (.up ℤ)).obj P)
          ((C.mapHomologicalComplex (.up ℤ)).obj Q) FB a b n h ≫ (tC P Q).hom.f n =
        (muC (P.X a) (Q.X b)).inv ≫
          C.map (CochainComplex.ιMapBifunctor P Q FA a b n h))
    (htI : ∀ (P Q : CochainComplex A ℤ) (a b n : ℤ) (h : a + b = n),
      CochainComplex.ιMapBifunctor ((I.mapHomologicalComplex (.up ℤ)).obj P)
          ((I.mapHomologicalComplex (.up ℤ)).obj Q) FD a b n h ≫ (tI P Q).hom.f n =
        (muI (P.X a) (Q.X b)).inv ≫
          I.map (CochainComplex.ιMapBifunctor P Q FA a b n h))
    (delta : ∀ M N : B, U.obj ((FB.obj M).obj N) ⟶ (FD.obj (U.obj M)).obj (U.obj N))
    (sigma : (Tot[FB]) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        (Tot[FD]))
    (hsigma : ∀ (P Q : CochainComplex B ℤ) (a b n : ℤ) (h : a + b = n),
      U.map (CochainComplex.ιMapBifunctor P Q FB a b n h) ≫
          (sigma.hom.app (P, Q)).f n =
        delta (P.X a) (Q.X b) ≫
          CochainComplex.ιMapBifunctor ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) FD a b n h)
    (hordinary : ∀ M N : A,
      U.map (muC M N).inv ≫ alpha.hom.app ((FA.obj M).obj N) =
        delta (C.obj M) (C.obj N) ≫
          (FD.map (alpha.hom.app M)).app (U.obj (C.obj N)) ≫
            (FD.obj (I.obj M)).map (alpha.hom.app N) ≫ (muI M N).inv)
    (P Q : CochainComplex A ℤ) :
    alphaC.hom.app ((Tot[FA]).obj (P, Q)) ≫ (tI P Q).inv =
      (U.mapHomologicalComplex (.up ℤ)).map (tC P Q).inv ≫
        sigma.hom.app (((C.mapHomologicalComplex (.up ℤ)).obj P),
          ((C.mapHomologicalComplex (.up ℤ)).obj Q)) ≫
            (Tot[FD]).map (Prod.mkHom (alphaC.hom.app P) (alphaC.hom.app Q)) := by
  rw [mapTotalBifunctor]
  apply (cancel_epi ((U.mapHomologicalComplex (.up ℤ)).map (tC P Q).hom)).1
  apply (cancel_mono (tI P Q).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  refine HomologicalComplex.mapBifunctor.hom_ext_of_map U (fun a b h ↦ ?_)
  rw [← U.map_comp_assoc, htC, U.map_comp, Category.assoc, halpha]
  dsimp only [Functor.uncurry_obj_obj, Functor.map₂HomologicalComplex]
  have hn := alpha.hom.naturality (CochainComplex.ιMapBifunctor P Q FA a b n h)
  dsimp only [Functor.comp_map] at hn
  rw [hn, ← Category.assoc, hordinary]
  simp only [Category.assoc]
  rw [reassoc_of% (hsigma _ _ a b n h)]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, htI]
  simp only [halpha]
  rfl

end HomologicalComplex
