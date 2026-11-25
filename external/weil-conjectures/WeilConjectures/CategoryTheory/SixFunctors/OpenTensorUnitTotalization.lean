/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-! # Totalization of the open tensor unit equation

Source: Stacks 012Z and 0GL1. The argument tests the equation on the actual
coproduct insertions of each homogeneous tensor summand.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
  [HasCountableCoproducts A] [HasCountableCoproducts B]
  (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
  (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B)
  [F.Additive] [∀ M, (F.obj M).Additive] [G.Additive] [∀ M, (G.obj M).Additive]
  (adj : E ⊣ R)

/-- Totalizing the sheaf unit equation gives the unit equation on complexes.
Source: Stacks 012Z, 0GL1 (blueprint: lem-sf-open-tensor-unit-totalization).
Proof: test on every homogeneous tensor summand. Naturality of the total tensor
moves the sheaf unit through its insertion. The restriction summand equation,
composed with the two inverses, identifies the inverse restriction map on that
summand. The open comparison summand equation then leaves exactly the sheaf
unit equation. Finally use naturality of the adjunction unit with respect to
the tensor insertion. The insertion maps jointly detect morphisms from the
coproduct total, and equality of chain maps is detected degreewise. -/
theorem openTensorUnitTotalization
    (sheafGamma : ∀ M N, (G.obj (E.obj M)).obj N ≅ E.obj ((F.obj M).obj (R.obj N)))
    (sheafRestriction : ∀ M N, R.obj ((G.obj M).obj N) ≅
      (F.obj (R.obj M)).obj (R.obj N))
    (hsheaf : ∀ M N, adj.homEquiv _ _ (sheafGamma M N).inv =
      (F.map (adj.unit.app M)).app (R.obj N) ≫
        (sheafRestriction (E.obj M) N).inv)
    (totalGamma : ∀ P T,
      (G.map₂CochainComplex.obj
          ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj T ≅
        (E.mapHomologicalComplex (.up ℤ)).obj
          ((F.map₂CochainComplex.obj P).obj ((R.mapHomologicalComplex (.up ℤ)).obj T)))
    (totalRestriction : ∀ P T,
      (R.mapHomologicalComplex (.up ℤ)).obj ((G.map₂CochainComplex.obj P).obj T) ≅
      (F.map₂CochainComplex.obj ((R.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (hgamma : ∀ P T (p q n : ℤ) (h : p + q = n),
      HomologicalComplex.ιMapBifunctor
          ((E.mapHomologicalComplex (.up ℤ)).obj P) T G (.up ℤ) p q n h ≫
        (totalGamma P T).hom.f n =
      (sheafGamma (P.X p) (T.X q)).hom ≫ E.map
        (HomologicalComplex.ιMapBifunctor P
          ((R.mapHomologicalComplex (.up ℤ)).obj T) F (.up ℤ) p q n h))
    (hrho : ∀ P T (p q n : ℤ) (h : p + q = n),
      R.map (HomologicalComplex.ιMapBifunctor P T G (.up ℤ) p q n h) ≫
          (totalRestriction P T).hom.f n =
        (sheafRestriction (P.X p) (T.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((R.mapHomologicalComplex (.up ℤ)).obj P)
            ((R.mapHomologicalComplex (.up ℤ)).obj T) F (.up ℤ) p q n h)
    (P : CochainComplex A ℤ) (T : CochainComplex B ℤ) :
    (F.map₂CochainComplex.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)).app
        ((R.mapHomologicalComplex (.up ℤ)).obj T) ≫
      (totalRestriction ((E.mapHomologicalComplex (.up ℤ)).obj P) T).inv ≫
      (R.mapHomologicalComplex (.up ℤ)).map (totalGamma P T).hom =
    (adj.mapHomologicalComplex (.up ℤ)).unit.app
      ((F.map₂CochainComplex.obj P).obj ((R.mapHomologicalComplex (.up ℤ)).obj T)) := by
  dsimp only [Functor.map₂CochainComplex, Functor.map₂HomologicalComplex] at *
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  let EP := (E.mapHomologicalComplex (.up ℤ)).obj P
  let RT := (R.mapHomologicalComplex (.up ℤ)).obj T
  have hr := hrho EP T p q n h
  have hr' : HomologicalComplex.ιMapBifunctor
        ((R.mapHomologicalComplex (.up ℤ)).obj EP) RT F (.up ℤ) p q n h ≫
        (totalRestriction EP T).inv.f n =
      (sheafRestriction (EP.X p) (T.X q)).inv ≫
        R.map (HomologicalComplex.ιMapBifunctor EP T G (.up ℤ) p q n h) := by
    apply (cancel_mono ((totalRestriction EP T).hom.f n)).1
    simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
      HomologicalComplex.id_f]
    rw [hr, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    change HomologicalComplex.ιMapBifunctor
        ((R.mapHomologicalComplex (.up ℤ)).obj EP) RT F (.up ℤ) p q n h ≫ 𝟙 _ =
      HomologicalComplex.ιMapBifunctor
        ((R.mapHomologicalComplex (.up ℤ)).obj EP) RT F (.up ℤ) p q n h
    exact Category.comp_id _
  have hs := hsheaf (P.X p) (T.X q)
  rw [Adjunction.homEquiv_unit] at hs
  have hs' : (F.map (adj.unit.app (P.X p))).app (R.obj (T.X q)) ≫
        (sheafRestriction (EP.X p) (T.X q)).inv ≫
        R.map (sheafGamma (P.X p) (T.X q)).hom =
      adj.unit.app ((F.obj (P.X p)).obj (R.obj (T.X q))) := by
    change (F.map (adj.unit.app (P.X p))).app (R.obj (T.X q)) ≫
        (sheafRestriction (E.obj (P.X p)) (T.X q)).inv ≫
        R.map (sheafGamma (P.X p) (T.X q)).hom = _
    rw [← Category.assoc, ← hs, Category.assoc, ← R.map_comp, Iso.inv_hom_id,
      R.map_id]
    exact Category.comp_id _
  change HomologicalComplex.ιMapBifunctor P RT F (.up ℤ) p q n h ≫
      (HomologicalComplex.mapBifunctorMap
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) (𝟙 RT) F (.up ℤ)).f n ≫
      (totalRestriction EP T).inv.f n ≫ R.map ((totalGamma P T).hom.f n) =
    HomologicalComplex.ιMapBifunctor P RT F (.up ℤ) p q n h ≫ adj.unit.app _
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f, Functor.map_id, Category.id_comp]
  rw [← Category.assoc _ _ (R.map ((totalGamma P T).hom.f n))]
  erw [hr']
  simp only [Category.assoc]
  rw [← R.map_comp, hgamma P T p q n h, R.map_comp]
  have hs'' : (F.map (((adj.mapHomologicalComplex (.up ℤ)).unit.app P).f p)).app
        (RT.X q) ≫ (sheafRestriction (EP.X p) (T.X q)).inv ≫
        R.map (sheafGamma (P.X p) (T.X q)).hom =
      adj.unit.app ((F.obj (P.X p)).obj (R.obj (T.X q))) := by
    change (F.map (adj.unit.app (P.X p))).app (R.obj (T.X q)) ≫
      (sheafRestriction (E.obj (P.X p)) (T.X q)).inv ≫
      R.map (sheafGamma (P.X p) (T.X q)).hom = _
    exact hs'
  rw [← Category.assoc] at hs''
  rw [← Category.assoc, ← Category.assoc]
  erw [hs'']
  exact (adj.unit.naturality
    (HomologicalComplex.ιMapBifunctor P RT F (.up ℤ) p q n h)).symm

end CategoryTheory
