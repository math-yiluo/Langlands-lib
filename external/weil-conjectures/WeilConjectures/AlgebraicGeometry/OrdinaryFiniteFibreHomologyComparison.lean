/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField

/-! # Homology of a direct image to a geometric point

Source: blueprint lemma-cohomology-projective-line-trace, geometric-fibre calculation.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option allowUnsafeReducibility true in
attribute [local reducible] ordinaryFiniteDegreeZero ordinaryFiniteLine ordinaryFiniteUnit

attribute [-instance] CategoryTheory.catToReflQuiver in
private def kummer_homology_shift_iso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (n q : ℤ) (hq : 2 + n = q) :
    (DerivedCategory.homologyFunctor C n).obj (K⟦(2 : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor C q).obj K := by
  simpa only [Functor.comp_obj, DerivedCategory.shift_homologyFunctor] using
    (((DerivedCategory.homologyFunctor C 0).shiftIso 2 n q hq).app K)

/-- The canonical comparison between sections of a homology sheaf over a
separably closed point and shifted cohomology on the source.
Source: blueprint lemma-cohomology-projective-line-trace, the geometric-fibre calculation.
(auxiliary; not a blueprint node).

Construction: commute derived direct image with the shift, apply the homology
shift comparison, commute exact sections over the separably closed point with
homology, identify derived sections on that point, and compose derived direct
image with derived global sections. Each factor is the library's specified
comparison isomorphism. -/
def ordinaryFinitePushforward_single_shift_homology_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (n q : ℤ) (hq : 2 + n = q) :
    (constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.obj
      ((DerivedCategory.homologyFunctor _ n).obj
        ((ordinaryFinitePushforward A a).obj
          (((DerivedCategory.singleFunctor _ 0).obj F)⟦(2 : ℤ)⟧))) ≅
    (cohomology (ModuleCat.{u + 1} A) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F) := by
  unfold ordinaryFinitePushforward
  letI : (constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.Additive :=
    show (((sheafSections (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} A)).obj (op (Scheme.etalePoint k)))).Additive from inferInstance
  let G := (constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse
  let K := (DerivedCategory.singleFunctor _ 0).obj F
  let R := (lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctor
  let _ : R.CommShift ℤ := by
    simpa only [R, ordinaryFinitePushforward] using
      commShiftRightDerivedLowerStar (ModuleCat.{u + 1} A) a
  let sh : (DerivedCategory.homologyFunctor _ n).obj ((R.obj K)⟦(2 : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor _ q).obj (R.obj K) := by
    simpa only [Functor.comp_obj, DerivedCategory.shift_homologyFunctor] using
      (((DerivedCategory.homologyFunctor _ 0).shiftIso 2 n q hq).app (R.obj K))
  exact G.mapIso ((DerivedCategory.homologyFunctor _ n).mapIso
      ((R.commShiftIso (2 : ℤ)).app K) ≪≫
    sh) ≪≫
    (G.mapDerivedCategoryHomologyFunctorIso q).app (R.obj K) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedGlobalSectionsIsoOfIsSepClosed A).app (R.obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} A) a).app K)

end AlgebraicGeometry.Etale
