/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1CoefficientCoordinateDefinitions
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Finite projective-line adjunction transport

Source: blueprint latest, diagonal-tower trace proof (1), identification of
finite coefficient units and direct images before the Chern-class calculation.
(blueprint: lem-sfb-finite-p1-adjunction-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

/-- Realize the ordinary intrinsic pullback by uniqueness of its left adjoint.
Source: Stacks Tags 00YV and 03D3, and the private nativePullRealization proof in
DiagonalTraceUnitArrowComparison (blueprint: lem-sfb-finite-p1-adjunction-transport). -/
def finiteNativePullCoordinate (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (Scheme.sfIntrinsicModuleEquivalence S A).functor.mapDerivedCategory ⋙
        Scheme.proEtaleConstantRingDerivedPullback A f ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategory ⋙
        (Scheme.sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory := by
  have hr : Scheme.proEtaleRingDirectImageMap f (Scheme.proEtaleConstantRing S A)
      (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRingComparison f A) =
        Scheme.proEtaleCoefficientDirectImageMap f A :=
    ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  let r : Scheme.proEtaleConstantRingPushforward A f ≅
      Scheme.proEtaleConstantModuleDirectImage f A :=
    SheafOfModules.pushforwardCongr (by rw [hr])
  let d := ((Scheme.proEtaleConstantRingAdjunction A f).ofNatIsoRight r).leftAdjointUniq
    (Scheme.sfIntrinsicConstantModuleAdjunction f A)
  let e := Scheme.sfIntrinsicModuleEquivalence S A
  let H := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let K := (Scheme.sfIntrinsicModuleEquivalence X A).functor
  exact Functor.isoWhiskerLeft e.functor.mapDerivedCategory
      (Functor.mapDerivedCategoryNatIso d) ≪≫
    Functor.mapDerivedCategoryCompIso e.functor (Scheme.sfIntrinsicPullback A f) ≪≫
    Functor.mapDerivedCategoryNatIso (e.funInvIdAssoc (H ⋙ K)) ≪≫
    (Functor.mapDerivedCategoryCompIso H K).symm

/-- Compose realization with pullback along the specified isomorphism over the base.
Source: diagonal-tower trace (1), and linePullRealization in
DiagonalTraceUnitArrowComparison (blueprint: lem-sfb-finite-p1-adjunction-transport). -/
def finiteProjectionPullCoordinate (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (e : X ≅ ProjectiveLine S)
    (he : e.hom ≫ (ProjectiveLine S ↘ S) = f) :
    (Scheme.sfIntrinsicModuleEquivalence S A).functor.mapDerivedCategory ⋙
        Scheme.proEtaleConstantRingDerivedPullback A f ≅
      geoP1Pullback (ULift.{u + 1} A) (ProjectiveLine S ↘ S) ⋙
        (geoP1Pullback (ULift.{u + 1} A) e.hom ⋙
          (Scheme.sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory) := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let p := ProjectiveLine S ↘ S
  let H := (upperStar C e.hom).mapDerivedCategory
  let K := (Scheme.sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory
  let t : upperStar C f ≅ upperStar C p ⋙ upperStar C e.hom :=
    eqToIso (congrArg (fun h : X ⟶ S ↦ upperStar C h) he.symm) ≪≫
      upperStarComp C e.hom p
  exact finiteNativePullCoordinate A f ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso t ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar C p) (upperStar C e.hom)).symm) K ≪≫
    Functor.associator (upperStar C p).mapDerivedCategory H K ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory C p).symm (H ⋙ K) ≪≫
    Functor.isoWhiskerLeft (geoP1Pullback (ULift.{u + 1} A) p)
      (Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory C e.hom).symm K)

/-- Transport an inverse-image comparison across equivalences and take its mate.
Source: Mathlib unit_mateEquiv and the equivalence-mate theorem
(blueprint: lem-sfb-finite-p1-adjunction-transport).
Proof: the mate is invertible because both vertical functors are equivalences.
Its inverse is the direct-image coordinate. Postcompose the mate unit identity
with that inverse and cancel the resulting inverse/hom pair. -/
theorem finiteAdjunctionCoordinates
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (F : C ⥤ C') (H : D ⥤ D')
    [F.IsEquivalence] [H.IsEquivalence] (p : F ⋙ L' ≅ L ⋙ H) :
    ∃ q : H ⋙ R' ≅ R ⋙ F,
      ∀ M, b.unit.app (F.obj M) ≫ R'.map (p.hom.app M) ≫
        q.hom.app (L.obj M) = F.map (a.unit.app M) := by
  let m := (mateEquiv a b (TwoSquare.mk _ _ _ _ p.hom))
  have : IsIso m := isIso_mateEquiv_of_isEquivalence a b _
  refine ⟨(asIso m).symm, ?_⟩
  intro M
  have h := unit_mateEquiv a b (TwoSquare.mk _ _ _ _ p.hom) M
  change F.map (a.unit.app M) ≫ m.app (L.obj M) =
    b.unit.app (F.obj M) ≫ R'.map (p.hom.app M) at h
  rw [← Category.assoc, ← h, Category.assoc]
  change F.map (a.unit.app M) ≫
    ((asIso m).hom.app (L.obj M) ≫ (asIso m).inv.app (L.obj M)) = _
  rw [Iso.hom_inv_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.ProEtale.DiagonalTrace
