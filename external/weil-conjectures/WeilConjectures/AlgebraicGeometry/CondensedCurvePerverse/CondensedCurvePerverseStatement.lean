/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ExactSequence

/-! # The perverse heart on a smooth curve with condensed coefficients

Source: latest blueprint, sec-wft-perverse/
sk-lem-wft-curve-heart/_section.md and sk-lem-wft-curve-heart.proof.md.
(blueprint: lemma-perverse-sheaves-curve)

The two classes are defined by ordinary module-sheaf cohomology. Finite closed support
is expressed by zero restriction off a finite set of closed points. The geometric
category is exactly the recorded finite-constant-model bounded constructible category.
Weil objects are fixed pairs for the ordinary derived module inverse image whose
carriers lie in the geometric heart. For rational coefficients Dctf equals Dbc.
All support tests and subobjects in the two classes are geometric.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverse

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual category of modules over the pulled-back condensed coefficient ring.
Source: current blueprint, ambient category in lemma-perverse-sheaves-curve
(blueprint: lemma-perverse-sheaves-curve). -/
abbrev Modules (C : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C)

/-- A constructible sheaf is punctual when it vanishes off a finite set of closed points.
This includes the zero sheaf and allows the empty finite set. Zero inverse image on the
complement is the support condition for a sheaf, with no choice of a geometric stalk.
Source: current blueprint lemma-perverse-sheaves-curve, opening definition
(blueprint: lemma-perverse-sheaves-curve). -/
def IsPunctual (C : Scheme.{u}) (F : Modules Λ C) : Prop :=
  IsConstantModelConstructible Λ C F ∧
    ∃ U : C.Opens, ((U : Set C)ᶜ).Finite ∧
      (∀ x ∈ (U : Set C)ᶜ, IsClosed ({x} : Set C)) ∧
      IsZero ((CondensedRing.upperStar Λ U.ι).obj F)

/-- Absence of a nonzero punctual subsheaf is tested on geometric module monomorphisms,
without imposing a Weil structure on the subobject.
Source: current blueprint lemma-perverse-sheaves-curve, lower-class formula
(blueprint: lemma-perverse-sheaves-curve). -/
def HasNoPunctualSubsheaf (C : Scheme.{u}) (F : Modules Λ C) : Prop :=
  ∀ (G : Modules Λ C) (i : G ⟶ F), Mono i → IsPunctual Λ C G → IsZero G

/-- The upper curve class at n: cohomology above n vanishes and H^n is punctual.
This is the shift by -n of the displayed class at zero.
Source: current blueprint lemma-perverse-sheaves-curve, first displayed class
(blueprint: lemma-perverse-sheaves-curve). -/
def upper (C : Scheme.{u}) (n : ℤ) : ObjectProperty (DerivedCategory (Modules Λ C)) :=
  fun K ↦ (∀ a : ℤ, n < a → IsZero ((DerivedCategory.homologyFunctor _ a).obj K)) ∧
    IsPunctual Λ C ((DerivedCategory.homologyFunctor _ n).obj K)

/-- The lower curve class at n: cohomology below n-1 vanishes and H^(n-1) has no
nonzero punctual subsheaf. This is the shift by -n of the displayed class at zero.
Source: current blueprint lemma-perverse-sheaves-curve, second displayed class
(blueprint: lemma-perverse-sheaves-curve). -/
def lower (C : Scheme.{u}) (n : ℤ) : ObjectProperty (DerivedCategory (Modules Λ C)) :=
  fun K ↦ (∀ a : ℤ, a < n - 1 → IsZero ((DerivedCategory.homologyFunctor _ a).obj K)) ∧
    HasNoPunctualSubsheaf Λ C ((DerivedCategory.homologyFunctor _ (n - 1)).obj K)

/-- The perverse heart, retaining its ambient geometric derived morphisms.
Source: current blueprint lemma-perverse-sheaves-curve, heart definition
(blueprint: lemma-perverse-sheaves-curve). -/
def heart (C : Scheme.{u}) : ObjectProperty (DerivedCategory (Modules Λ C)) :=
  constantModelBoundedConstructible Λ C ⊓ (upper Λ C 0 ⊓ lower Λ C 0)

/-- Perverse Weil sheaves are the full subcategory of the recorded strict Weil pairs
whose underlying geometric complex lies in the perverse heart.
Source: current blueprint lemma-perverse-sheaves-curve, Weil definition paragraph
(blueprint: lemma-perverse-sheaves-curve). -/
abbrev WeilHeart {C : Scheme.{u}} (g : C ≅ C) :=
  ObjectProperty.FullSubcategory
    (fun K : Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ g.hom).mapDerivedCategory ↦
      heart Λ C K.carrier)

/-- The canonical forgetful functor retains the carrier and its geometric derived arrow.
The defining carrier property supplies exactly bounded constructibility and the
geometric perverse conditions. Source: current blueprint lemma-perverse-sheaves-curve, final
paragraph (blueprint: lemma-perverse-sheaves-curve). -/
def forget {C : Scheme.{u}} (g : C ≅ C) :
    WeilHeart Λ g ⥤ (heart Λ C).FullSubcategory where
  obj K := ⟨K.obj.carrier, K.property⟩
  map f := ObjectProperty.homMk f.hom.hom.f

end AlgebraicGeometry.ProEtale.CondensedCurvePerverse
