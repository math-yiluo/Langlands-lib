/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.CategoryTheory.Derived.DerivedLocalizingPerfectFamily
import WeilConjectures.CategoryTheory.Perfect.PerfectFamilyWeakUniversal
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-! # Solution sets on set-generated localizing subcategories

Source: Neeman, *On the derived category of sheaves on a manifold*, Theorem 0.2;
Krause, *Localization theory for triangulated categories*, 7.2.1 and the construction
in 5.1.1; Krause, *Derived categories, resolutions, and Brown representability*, 4.5.
(blueprint: lem-sfb-set-generated-derived-solution-set)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

private theorem solutionSet_generators_detect_zero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    (P Q : ObjectProperty (DerivedCategory A))
    [Q.IsClosedUnderIsomorphisms] [Q.IsTriangulated]
    (hminimal : ∀ R : ObjectProperty (DerivedCategory A), P ≤ R →
      R.IsClosedUnderIsomorphisms → R.IsTriangulated →
      (∀ I : Type v, R.IsClosedUnderColimitsOfShape (Discrete I)) → Q ≤ R)
    {J : Type v} (S : J → Q.FullSubcategory)
    (hshift : ∀ (j : J) (n : ℤ), ∃ k, Nonempty (S k ≅ (S j)⟦n⟧))
    (hrep : ∀ X (_hX : P X), ∃ j, Nonempty (X ≅ (S j).obj))
    (X : Q.FullSubcategory) (hX : ∀ j (f : S j ⟶ X), f = 0) : IsZero X := by
  let B : ObjectProperty (DerivedCategory A) := .ofObj (fun j ↦ (S j).obj)
  let K := (B.shiftClosure ℤ).rightOrthogonal
  let R := K.leftOrthogonal
  have hRcoprod (I : Type v) : R.IsClosedUnderColimitsOfShape (Discrete I) := by
    constructor
    rintro Y ⟨c⟩ Z f hZ
    apply c.isColimit.hom_ext
    intro i
    change c.ι.app i ≫ f = c.ι.app i ≫ 0
    rw [comp_zero]
    exact c.prop_diag_obj i (c.ι.app i ≫ f) hZ
  have hBR : B ≤ R := by
    rintro _ ⟨j⟩ Y f hY
    exact hY f (B.le_shiftClosure _ ⟨j⟩)
  have hPR : P ≤ R := by
    intro Y hY
    obtain ⟨j, ⟨e⟩⟩ := hrep Y hY
    exact R.prop_of_iso e.symm (hBR _ ⟨j⟩)
  have hQR : Q ≤ R := hminimal R hPR inferInstance inferInstance hRcoprod
  have hKX : K X.obj := by
    intro Y f hY
    obtain ⟨Z, n, e, hZ⟩ := hY
    obtain ⟨j⟩ := hZ
    obtain ⟨k, ⟨s⟩⟩ := hshift j n
    let d : (S k).obj ≅ Y :=
      Q.ι.mapIso s ≪≫ (Q.ι.commShiftIso n).app (S j) ≪≫ e.symm
    have hf := hX k (ObjectProperty.homMk (d.hom ≫ f))
    have hf' : d.hom ≫ f = 0 := congrArg (fun g ↦ Q.ι.map g) hf
    apply (cancel_epi d.hom).1
    simpa using hf'
  have hid : 𝟙 X.obj = 0 := hQR X.obj X.property (𝟙 X.obj) hKX
  apply (IsZero.iff_id_eq_zero X).2
  apply Q.ι.map_injective
  simpa using hid

/-- The elements of a product-preserving cohomological functor on a set-generated
localizing subcategory of a Grothendieck derived category have a small weakly
universal family. This asserts neither uniqueness nor a representing object.

Source: Neeman, *On the derived category of sheaves on a manifold*, Theorem 0.2;
Krause, *Localization theory for triangulated categories*, Theorems 7.2.1 and 5.1.1;
the cellular construction in Krause, *Derived categories, resolutions, and Brown
representability*, Section 4.5.
(blueprint: lem-sfb-set-generated-derived-solution-set)

Proof: choose an ambient essentially small replete triangulated perfect class
containing P, with bounded-subcoproduct factorization, using Neeman 0.2 and Krause
Sections 6.2-6.3. Intersect it with Q. The proved localizing-hull factorization
argument and minimality give a small shift-closed perfect family in Q containing
representatives of P. To see that it detects zero objects, let K be the right
orthogonal of its shift closure. The left orthogonal of K is localizing and
contains P, hence contains Q. An object of Q orthogonal to the family then has
zero identity.

For each pair (W,w), adjoin the coproduct of all pairs (generator, H-element).
Iteratively attach cones of all generator maps killed by the current element.
Product preservation and cohomological exactness lift the element at each stage
and to the sequential telescope. Perfectness gives coproduct weak kernels;
comparison with constant sequences, whose telescope maps have explicit
retractions, makes evaluation at the lifted element bijective on all generators.
Start at W=0 to obtain (X,x). For an arbitrary pair (Y,y), repeat the construction
starting at X plus Y. The map from X to the new telescope preserves elements and
is bijective on Hom from the generators. Its cone is zero by shift closure and
triangle exactness, so it is invertible. Compose the map from Y with this inverse
to pull x back to y. Thus the singleton family (X,x) is a solution set.
Every index used is v-small: the perfect family, Hom sets and H-values are in
universe v. No compactness of the original P is used.
-/
theorem setGeneratedDerived_cohomological_solutionSet
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (P Q : ObjectProperty (DerivedCategory A))
    [ObjectProperty.EssentiallySmall.{v} P]
    [Q.IsClosedUnderIsomorphisms] [Q.IsTriangulated]
    [∀ I : Type v, Q.IsClosedUnderColimitsOfShape (Discrete I)]
    (hP : P ≤ Q)
    (hminimal : ∀ R : ObjectProperty (DerivedCategory A), P ≤ R →
      R.IsClosedUnderIsomorphisms → R.IsTriangulated →
      (∀ I : Type v, R.IsClosedUnderColimitsOfShape (Discrete I)) → Q ≤ R)
    (H : Q.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H) :
    ∃ (I : Type v) (B : I → Q.FullSubcategory) (b : ∀ i, H.obj (op (B i))),
      ∀ (Z : Q.FullSubcategory) (z : H.obj (op Z)), ∃ (i : I) (f : Z ⟶ B i),
        H.map f.op (b i) = z := by
  have : HasCoproducts.{v} (DerivedCategory A) := derived_hasCoproducts
  obtain ⟨J, S, hshift, hrep, hperfect⟩ :=
    setGeneratedDerived_exists_perfectFamily P Q hP hminimal
  have hzero := solutionSet_generators_detect_zero P Q hminimal S hshift hrep
  obtain ⟨X, x, hx⟩ := perfectFamily_exists_weakUniversal S hshift hzero hperfect H hH
  exact ⟨PUnit.{v + 1}, fun _ ↦ X, fun _ ↦ x, fun Z z ↦ by
    obtain ⟨f, hf⟩ := hx Z z
    exact ⟨PUnit.unit, f, hf⟩⟩

end CategoryTheory
