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
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.Derived.DerivedPerfectSmallClassCore
import WeilConjectures.CategoryTheory.Derived.DerivedPerfectSmallClassProperties

/-! # Small perfect classes in Grothendieck derived categories

Source: Neeman, On the derived category of sheaves on a manifold, Theorem 0.2;
Krause, Localization theory for triangulated categories, Sections 6.2-6.3.
(blueprint: lem-sfb-derived-perfect-small-class)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Every small family in D(A) lies in an essentially small replete triangulated
perfect class, with bounded-subcoproduct factorization for its own objects.

Source: Neeman, *On the derived category of sheaves on a manifold*, Theorem 0.2;
Krause, *Localization theory for triangulated categories*, Sections 6.2-6.3 and
Proposition 6.8.1.
(blueprint: lem-sfb-derived-perfect-small-class)

Proof: choose v-small representatives P₀ of P. Neeman's Theorem 0.2 makes D(A)
well generated. Its proof presents D(A) as D(R)/Loc(L) for a set of complexes L,
using Gabriel-Popescu; the module derived category is compactly generated and
localization by a set is well generated. By Krause Section 6.3, every object is
beta-compact for some regular beta and D(A) is alpha-well generated for every
sufficiently large regular alpha. Bound the set of cardinals for P₀ by a common
uncountable regular alpha above a well-generation bound for D(A).

Take S = D(A)^alpha, the class of alpha-compact objects. This class is essentially
v-small, replete, triangulated, and contains P₀ and hence P. Section 6.3 and
Proposition 6.8.1 show that it is perfect: componentwise surjectivity on Hom from
all its objects remains surjective after every v-small coproduct. It is also
alpha-localizing and all its objects are alpha-small. Therefore a map from U in S
to a coproduct of objects Y_i in S factors through a subcoproduct indexed by a
subset J of I with cardinality less than alpha. This subcoproduct lies in S by
alpha-localizing closure. Take a:J to I to be the inclusion and g the factorization;
the displayed Sigma.desc is exactly the subcoproduct inclusion. Every cardinal,
skeleton, Hom set, and index here is in universe v. No localizing subcategory Q
or cohomological functor enters this ambient assertion.

References: https://ems.press/journals/dm/articles/8965042, Theorem 0.2 and Section 2;
https://webhomes.maths.ed.ac.uk/~v1ranick/papers/krause2.pdf, Sections 6.2-6.3 and 6.8.
-/
theorem derived_exists_perfectSmallClass
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (P : ObjectProperty (DerivedCategory A))
    [ObjectProperty.EssentiallySmall.{v} P] :
    ∃ S : ObjectProperty (DerivedCategory A),
      ObjectProperty.EssentiallySmall.{v} S ∧ S.IsClosedUnderIsomorphisms ∧
      S.IsTriangulated ∧ P ≤ S ∧
      (∀ (I : Type v) (X Y : I → DerivedCategory A) (f : ∀ i, X i ⟶ Y i),
        (∀ i U, S U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) →
        ∀ U, S U → Function.Surjective
          (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f)) ∧
      (∀ (I : Type v) (Y : I → DerivedCategory A), (∀ i, S (Y i)) →
        ∀ (U : DerivedCategory A), S U → ∀ f : U ⟶ ∐ Y,
        ∃ (J : Type v) (a : J → I), S (∐ fun j ↦ Y (a j)) ∧
          ∃ g : U ⟶ ∐ fun j ↦ Y (a j),
            g ≫ Sigma.desc (fun j ↦ Sigma.ι Y (a j)) = f) := by
  obtain ⟨S, α, hα, hS, hSi, hSt, hPS, hSsum, hcompact⟩ :=
    derived_exists_perfectSmallClass_core P
  let _ : Fact α.IsRegular := hα
  obtain ⟨hperfect, hfactor⟩ :=
    derived_perfectSmallClass_properties S α hSsum hcompact
  exact ⟨S, hS, hSi, hSt, hPS, hperfect, hfactor⟩

end CategoryTheory
