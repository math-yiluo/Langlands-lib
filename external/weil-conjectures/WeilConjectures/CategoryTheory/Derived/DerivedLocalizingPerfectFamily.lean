/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.Derived.DerivedPerfectSmallClass
import WeilConjectures.CategoryTheory.Perfect.PerfectFamilyLocalizingHull

/-! # Perfect families in set-generated derived subcategories

Source: Neeman, Theorem 0.2; Krause, Localization theory, Theorem 7.2.1.
(blueprint: lem-sfb-derived-localizing-perfect-family)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- A set-generated localizing subcategory of a Grothendieck derived category admits
small, shift-closed perfect generators.

Source: Neeman, *On the derived category of sheaves on a manifold*, Theorem 0.2;
Krause, *Localization theory for triangulated categories*, Theorem 7.2.1 and
Section 5.1, conditions (PG1) and (PG2).
(blueprint: lem-sfb-derived-localizing-perfect-family)

Proof: choose an ambient essentially small replete triangulated perfect class S
containing P, with bounded-subcoproduct factorization. Put B = S intersect Q.
This class is replete, triangulated, essentially small, and contains P. A map
from S into a coproduct of B objects factors through a subcoproduct belonging
to S; that subcoproduct also belongs to Q by coproduct closure, hence to B.
Apply perfectFamily_of_small_hull. Its proof shows that the objects X for which
all maps from S to X factor through B form a localizing class. The extension
check uses two cone constructions and corrects the lift by a map through the
first vertex; the coproduct check uses evaluation covers, ambient perfectness,
and small factorization after flattening the covers. This class contains P,
so minimality makes it contain Q. Componentwise surjectivity on B consequently
implies it on S for maps in Q. Ambient perfectness then gives surjectivity on B
after coproducts. A small skeleton of B supplies J, its closure under shifts
supplies the displayed isomorphisms, and P <= B supplies the representatives.
The inclusion of Q is fully faithful and preserves the coproducts, so its
comparison isomorphisms transport the surjectivity to Q.FullSubcategory.

References: https://ems.press/journals/dm/articles/8965042 (Theorem 0.2);
https://webhomes.maths.ed.ac.uk/~v1ranick/papers/krause2.pdf, Theorem 7.2.1.
-/
theorem setGeneratedDerived_exists_perfectFamily
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (P Q : ObjectProperty (DerivedCategory A))
    [ObjectProperty.EssentiallySmall.{v} P]
    [Q.IsClosedUnderIsomorphisms] [Q.IsTriangulated]
    [∀ I : Type v, Q.IsClosedUnderColimitsOfShape (Discrete I)]
    (hP : P ≤ Q)
    (hminimal : ∀ R : ObjectProperty (DerivedCategory A), P ≤ R →
      R.IsClosedUnderIsomorphisms → R.IsTriangulated →
      (∀ I : Type v, R.IsClosedUnderColimitsOfShape (Discrete I)) → Q ≤ R) :
    ∃ (J : Type v) (S : J → Q.FullSubcategory),
      (∀ (j : J) (n : ℤ), ∃ k, Nonempty (S k ≅ (S j)⟦n⟧)) ∧
      (∀ X (_hX : P X), ∃ j, Nonempty (X ≅ (S j).obj)) ∧
      (∀ (I : Type v) (X Y : I → Q.FullSubcategory) (f : ∀ i, X i ⟶ Y i),
        (∀ i j, Function.Surjective (fun g : S j ⟶ X i ↦ g ≫ f i)) →
        ∀ j, Function.Surjective (fun g : S j ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f)) := by
  obtain ⟨S, hSs, hSi, hSt, hPS, hperfect, hsub⟩ :=
    derived_exists_perfectSmallClass P
  have := hSs
  have := hSi
  have := hSt
  let B := S ⊓ Q
  have : ObjectProperty.EssentiallySmall.{v} B :=
    ObjectProperty.EssentiallySmall.of_le (Q := S) inf_le_left
  have hsmall (U : DerivedCategory A) (hU : S U) (I : Type v)
      (Y : I → DerivedCategory A) (hY : ∀ i, B (Y i)) (f : U ⟶ ∐ Y) :
      ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ ∐ Y), g ≫ h = f := by
    obtain ⟨J, a, hS, g, hg⟩ := hsub I Y (fun i ↦ (hY i).1) U hU f
    have hQ : Q (∐ fun j ↦ Y (a j)) :=
      Q.prop_of_isColimit (coproductIsCoproduct (fun j ↦ Y (a j)))
        (fun j ↦ (hY (a j.as)).2)
    exact ⟨_, ⟨hS, hQ⟩, g, _, hg⟩
  exact perfectFamily_of_small_hull S B inf_le_left P Q
    (fun X hX ↦ ⟨hPS X hX, hP X hX⟩) inf_le_right hminimal hperfect hsmall

end CategoryTheory
