/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver
public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.RelativeTorPullbackTensorLowerBound
import WeilConjectures.AlgebraicGeometry.ProperSupportDerivedProjectionFormula
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.Algebra.Homology.KFlatResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Uniform lower tensor bound for a proper-support direct image

Source: Stacks Project, Tag 08EV, proof, the quasi-compact support reduction,
projection formula, and the lower bound after applying the right-derived direct image.
(blueprint: lem-pc-proper-direct-image-tensor-lower-bound)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable local instance (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  SheafOfModules.monoidalCategory Y.sheaf

private theorem directImage_isGE {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X) (a : ℤ) [E.IsGE a] :
    ((schemeDerivedDirectImage f).obj E).IsGE a := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  have : IsGrothendieckAbelian.{u} C := RingedSpace.moduleGrothendieckAbelian X.toRingedSpace
  let G := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let Eplus : DerivedCategory.Plus C := ⟨E, a, inferInstance⟩
  have hE : (DerivedCategory.Plus.ι.obj Eplus).IsGE a :=
    show E.IsGE a from inferInstance
  have : Eplus.IsGE a := (Eplus.isGE_ι_obj_iff a).1 hE
  refine (DerivedCategory.isGE_iff _ a).2 fun i hi ↦ ?_
  exact (G.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE Eplus a hi).of_iso
    ((DerivedCategory.homologyFunctor D i).mapIso
      (G.rightDerivedFunctorPlusCompatibility.app Eplus)).symm

private theorem tensor_vanishes_of_isZero (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory Y)
    (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (MonoidalCategory.tensorObj E ((DerivedCategory.singleFunctor _ 0).obj F)))) :
    schemeDerivedTensorCohomologyVanishes Y E F i := by
  let K := DerivedCategory.Q.objPreimage E
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf) K
  have : QuasiIso s := hs
  let eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  let N := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F
  obtain ⟨cmp⟩ := kFlat_derivedTensor_comparison_natIso Y
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hP)
  let e : MonoidalCategory.tensorObj E ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N (MonoidalCategory.curriedTensor _)) :=
    (MonoidalCategory.tensorIso eP (Iso.refl (DerivedCategory.Q.obj N))).symm ≪≫
      (cmp.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  exact ⟨P, hP, ⟨eP⟩, h.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _).symm⟩

/-- Proper-support direct image gives a uniform lower bound after tensoring with
quasi-coherent modules. No upper bound or arbitrary-module test is asserted here.
Source: Stacks Project, Tag 08EV, proof, lower-bound argument; Tags 08EU and 08DZ.
(blueprint: lem-pc-proper-direct-image-tensor-lower-bound)

Proof:
1. Boundedness leaves finitely many nonzero cohomology sheaves. Their supports have
   proper union over S. Choose a quasi-compact open U containing this union. Restriction
   to U is exact, preserves coherence and the finite Tor interval over the inverse-image
   structure sheaf, and leaves the derived direct image unchanged. The restricted morphism
   is quasi-compact and quasi-separated, since S is Noetherian and f locally of finite type.
   This is the geometric and exact-restriction argument of directImage_qc_support_reduction;
   choose a derived localization on U and compare it with the fixed localizations on X and S.
2. Fix a quasi-coherent module F on S. Resolve F by a bounded-above flat complex L
   zero in positive degrees, using bounded flat replacement. Its termwise pullback
   represents Lf*F and is K-flat. Associativity of tensor identifies
   E tensor^L_{O_X} Lf*F with E tensor^L_{f^{-1}O_S} f^{-1}F: inverse image is exact,
   the inverse images of the flat terms of L are flat, and bounded-above flat complexes
   are K-flat. Thus the finite Tor interval [a,b] of E bounds this object, uniformly in F.
3. E has quasi-coherent cohomology, and derived pullback and tensor preserve this property.
   The projection formula identifies Rf*E tensor^L F with the derived direct image
   of the object in step 2. A bounded-below K-injective resolution can be taken zero
   below a; termwise direct image remains zero below a. Its cohomology consequently
   vanishes there. Transport back through the support-reduction isomorphism and choose
   a K-flat representative of Rf*E to express this vanishing with the stated predicate.
   The integer a comes from E's finite Tor interval, so it is independent of F. -/
theorem exists_schemeDerivedDirectImage_tensor_lower_bound
    (S : Scheme.{u}) [IsNoetherian S]
    (X : Scheme.{u}) (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hTor : HasFiniteTorDimensionOver f E) :
    ∃ a : ℤ, ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      F.IsQuasicoherent → ∀ i : ℤ, i < a →
        schemeDerivedTensorCohomologyVanishes S ((schemeDerivedDirectImage f).obj E) F i := by
  obtain ⟨a, ha⟩ := exists_relativeTor_pullback_tensor_lower_bound f E hTor
  refine ⟨a, fun F hF i hi ↦ ?_⟩
  have := ha F
  have := directImage_isGE f
    (MonoidalCategory.tensorObj E
      ((derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) a
  obtain ⟨e⟩ := nonempty_properSupport_derivedProjection_iso
    S X f E hbounded hcoherent hsupport F hF
  apply tensor_vanishes_of_isZero S _ F i
  exact (DerivedCategory.isZero_of_isGE _ a i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e)

end AlgebraicGeometry.Scheme
