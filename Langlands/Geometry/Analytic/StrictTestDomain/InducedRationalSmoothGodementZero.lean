import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothGodementInvariants
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothCohomologyTransport
import Langlands.Cohomology.SmoothGodement.ZeroSpatial

/-! # Proper rational Godement maps recover the original compact functions in degree zero -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementCohomology
open Langlands.Cohomology.SmoothGodementCohomology.Spatial
open Langlands.Cohomology.SmoothGodementComparison

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type u} [CommRing R]

namespace OpenSubgroupTransport.Hom

open SmoothCohomology

variable {X Y Z : ρ.OpenSubgroupTransport}

/-- Restrict the original proper compact-function pullback to whole-group invariants. -/
def invariantCompactSupportPullbackNatTrans (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    invariantCompactFunctions (R := R) Y ⟶ invariantCompactFunctions X :=
  Functor.whiskerRight (compactSupportPullbackNatTrans f hf) (smoothInvariants R G)

/-- The original invariant compact function is pulled back by the actual induced map. -/
@[simp]
theorem invariantCompactSupportPullbackNatTrans_apply (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G)
    (s : (invariantCompactFunctions Y).obj M) (z : X.InducedSpectrum) :
    (((invariantCompactSupportPullbackNatTrans f hf).app M).hom s).val.val z =
      s.val.val (f.inducedMap z) := rfl

@[simp]
theorem invariantCompactSupportPullbackNatTrans_id :
    invariantCompactSupportPullbackNatTrans (R := R) (𝟙 X)
        (isProperMap_inducedMap_id X) = 𝟙 (invariantCompactFunctions X) := by
  simp [invariantCompactSupportPullbackNatTrans, invariantCompactFunctions]

/-- The restriction to invariant submodules preserves strict contravariant composition. -/
theorem invariantCompactSupportPullbackNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) :
    invariantCompactSupportPullbackNatTrans (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) =
      invariantCompactSupportPullbackNatTrans g hg ≫
        invariantCompactSupportPullbackNatTrans f hf := by
  apply NatTrans.ext
  funext M
  change (smoothInvariants R G).map _ = _
  rw [compactSupportPullbackNatTrans_comp f g hf hg]
  exact Functor.map_comp _ _ _

variable [HasStableNeighbourhoods G X.InducedSpectrum]
  [HasStableNeighbourhoods G Y.InducedSpectrum]
  [HasStableNeighbourhoods G Z.InducedSpectrum]

/-- The actual coefficient section map agrees with proper pullback of full compact functions. -/
@[reassoc]
theorem coefficientCompactSectionsNatTrans_toFunctions (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    coefficientCompactSectionsNatTrans f.inducedMap f.inducedMap_smul hf ≫
        (compactSectionsIso (R := R) X).inv =
      (compactSectionsIso Y).inv ≫ compactSupportPullbackNatTrans f hf := by
  apply NatTrans.ext
  funext M
  ext s
  rfl

/-- The same comparison holds after restriction to the actual invariant submodules. -/
@[reassoc]
theorem coefficientInvariantSectionsNatTrans_toFunctions (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    coefficientInvariantSectionsNatTrans f.inducedMap f.inducedMap_smul hf ≫
        (invariantCompactSectionsIso (R := R) X).inv =
      (invariantCompactSectionsIso Y).inv ≫
        invariantCompactSupportPullbackNatTrans f hf := by
  apply NatTrans.ext
  funext M
  ext s
  rfl

/-- Degree zero of the actual all-degree compact chain pullback is original compact pullback. -/
@[reassoc]
theorem godementCohomologyPullbackNatTrans_zero_toFunctions (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    godementCohomologyPullbackNatTrans (R := R) f hf 0 ≫
        (godementCompactCohomologyZeroIso X).hom =
      (godementCompactCohomologyZeroIso Y).hom ≫
        compactSupportPullbackNatTrans f hf := by
  change coefficientCohomologyNatTrans f.inducedMap f.inducedMap_smul hf 0 ≫
      ((Functor.isoWhiskerLeft (LocallyConstantSheaf.smoothFunctor R G X.InducedSpectrum)
        (smoothGodementCompactCohomologyZeroIso R G X.InducedSpectrum)).hom ≫
          (compactSectionsIso X).inv) =
    ((Functor.isoWhiskerLeft (LocallyConstantSheaf.smoothFunctor R G Y.InducedSpectrum)
        (smoothGodementCompactCohomologyZeroIso R G Y.InducedSpectrum)).hom ≫
          (compactSectionsIso Y).inv) ≫ compactSupportPullbackNatTrans f hf
  rw [← Category.assoc, coefficientCohomologyNatTrans_zero, Category.assoc,
    coefficientCompactSectionsNatTrans_toFunctions, Category.assoc]

/-- The all-degree constructed map equals the previously transported degree-zero map. -/
theorem godementCohomologyPullbackNatTrans_zero (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    godementCohomologyPullbackNatTrans (R := R) f hf 0 = godementZeroPullback f hf := by
  rw [← cancel_mono (godementCompactCohomologyZeroIso X).hom]
  rw [godementCohomologyPullbackNatTrans_zero_toFunctions, godementZeroPullback_toFunctions]

/-- Transport original invariant compact functions to the existing degree-zero Godement objects. -/
def godementInvariantZeroPullback (f : X ⟶ Y) (hf : IsProperMap f.inducedMap) :
    godementInvariantCompactCohomology (R := R) Y 0 ⟶
      godementInvariantCompactCohomology X 0 :=
  (godementInvariantCompactCohomologyZeroIso Y).hom ≫
    invariantCompactSupportPullbackNatTrans f hf ≫
      (godementInvariantCompactCohomologyZeroIso X).inv

/-- Transport the same original functions to the existing degree-zero sheaf-derived objects. -/
def invariantCompactDerivedZeroPullback (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    invariantCompactDerived (R := R) Y 0 ⟶ invariantCompactDerived X 0 :=
  (invariantCompactDerivedZeroIso Y).hom ≫
    invariantCompactSupportPullbackNatTrans f hf ≫
      (invariantCompactDerivedZeroIso X).inv

@[reassoc (attr := simp)]
theorem godementInvariantZeroPullback_toFunctions (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    godementInvariantZeroPullback (R := R) f hf ≫
        (godementInvariantCompactCohomologyZeroIso X).hom =
      (godementInvariantCompactCohomologyZeroIso Y).hom ≫
        invariantCompactSupportPullbackNatTrans f hf := by
  simp [godementInvariantZeroPullback, Category.assoc]

@[reassoc (attr := simp)]
theorem invariantCompactDerivedZeroPullback_toFunctions (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    invariantCompactDerivedZeroPullback (R := R) f hf ≫
        (invariantCompactDerivedZeroIso X).hom =
      (invariantCompactDerivedZeroIso Y).hom ≫
        invariantCompactSupportPullbackNatTrans f hf := by
  simp [invariantCompactDerivedZeroPullback, Category.assoc]

/-- The transported Godement map acts by precomposition on the original invariant functions. -/
@[simp]
theorem godementInvariantZeroPullback_apply (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G)
    (s : (godementInvariantCompactCohomology Y 0).obj M) (z : X.InducedSpectrum) :
    (((godementInvariantCompactCohomologyZeroIso X).hom.app M).hom
        (((godementInvariantZeroPullback f hf).app M).hom s)).val.val z =
      (((godementInvariantCompactCohomologyZeroIso Y).hom.app M).hom s).val.val
        (f.inducedMap z) := by
  have h := congrArg (fun b => (b.app M).hom s)
    (godementInvariantZeroPullback_toFunctions (R := R) f hf)
  exact congrArg (fun t => t.val.val z) h

/-- The transported sheaf-derived map has the same original invariant function formula. -/
@[simp]
theorem invariantCompactDerivedZeroPullback_apply (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G)
    (s : (invariantCompactDerived Y 0).obj M) (z : X.InducedSpectrum) :
    (((invariantCompactDerivedZeroIso X).hom.app M).hom
        (((invariantCompactDerivedZeroPullback f hf).app M).hom s)).val.val z =
      (((invariantCompactDerivedZeroIso Y).hom.app M).hom s).val.val
        (f.inducedMap z) := by
  have h := congrArg (fun b => (b.app M).hom s)
    (invariantCompactDerivedZeroPullback_toFunctions (R := R) f hf)
  exact congrArg (fun t => t.val.val z) h

@[simp]
theorem godementInvariantZeroPullback_id :
    godementInvariantZeroPullback (R := R) (𝟙 X) (isProperMap_inducedMap_id X) =
      𝟙 (godementInvariantCompactCohomology X 0) := by
  simp [godementInvariantZeroPullback]

@[simp]
theorem invariantCompactDerivedZeroPullback_id :
    invariantCompactDerivedZeroPullback (R := R) (𝟙 X) (isProperMap_inducedMap_id X) =
      𝟙 (invariantCompactDerived X 0) := by
  simp [invariantCompactDerivedZeroPullback]

theorem godementInvariantZeroPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) :
    godementInvariantZeroPullback (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) =
      godementInvariantZeroPullback g hg ≫ godementInvariantZeroPullback f hf := by
  simp [godementInvariantZeroPullback, invariantCompactSupportPullbackNatTrans_comp f g hf hg,
    Category.assoc, ← Category.assoc (godementInvariantCompactCohomologyZeroIso Y).inv
      (godementInvariantCompactCohomologyZeroIso Y).hom]

theorem invariantCompactDerivedZeroPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) :
    invariantCompactDerivedZeroPullback (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) =
      invariantCompactDerivedZeroPullback g hg ≫ invariantCompactDerivedZeroPullback f hf := by
  simp [invariantCompactDerivedZeroPullback,
    invariantCompactSupportPullbackNatTrans_comp f g hf hg, Category.assoc,
    ← Category.assoc (invariantCompactDerivedZeroIso Y).inv
      (invariantCompactDerivedZeroIso Y).hom]

/-- The actual degree-zero invariant Godement/derived identification commutes with transport. -/
@[reassoc (attr := simp)]
theorem godementInvariantDerivedZeroIso_pullback (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    godementInvariantZeroPullback (R := R) f hf ≫
        (godementInvariantDerivedZeroIso X).hom =
      (godementInvariantDerivedZeroIso Y).hom ≫
        invariantCompactDerivedZeroPullback f hf := by
  simp [godementInvariantZeroPullback, invariantCompactDerivedZeroPullback,
    godementInvariantDerivedZeroIso, Category.assoc,
    ← Category.assoc (godementInvariantCompactCohomologyZeroIso X).inv
      (godementInvariantCompactCohomologyZeroIso X).hom,
    ← Category.assoc (invariantCompactDerivedZeroIso Y).inv
      (invariantCompactDerivedZeroIso Y).hom]

/-- Invariants are applied before homology; in degree zero the actual map recovers invariant functions. -/
@[reassoc]
theorem godementInvariantCohomologyPullbackNatTrans_zero_toFunctions (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    godementInvariantCohomologyPullbackNatTrans (R := R) f hf 0 ≫
        (godementInvariantCompactCohomologyZeroIso X).hom =
      (godementInvariantCompactCohomologyZeroIso Y).hom ≫
        invariantCompactSupportPullbackNatTrans f hf := by
  change coefficientInvariantCohomologyNatTrans f.inducedMap f.inducedMap_smul hf 0 ≫
      ((Functor.isoWhiskerLeft (LocallyConstantSheaf.smoothFunctor R G X.InducedSpectrum)
        (smoothGodementInvariantCompactCohomologyZeroIso R G X.InducedSpectrum)).hom ≫
          (invariantCompactSectionsIso X).inv) =
    ((Functor.isoWhiskerLeft (LocallyConstantSheaf.smoothFunctor R G Y.InducedSpectrum)
        (smoothGodementInvariantCompactCohomologyZeroIso R G Y.InducedSpectrum)).hom ≫
          (invariantCompactSectionsIso Y).inv) ≫ invariantCompactSupportPullbackNatTrans f hf
  rw [← Category.assoc, coefficientInvariantCohomologyNatTrans_zero, Category.assoc,
    coefficientInvariantSectionsNatTrans_toFunctions, Category.assoc]

/-- The existing all-degree invariant map agrees with transport by the canonical zero isomorphisms. -/
theorem godementInvariantCohomologyPullbackNatTrans_zero (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    godementInvariantCohomologyPullbackNatTrans (R := R) f hf 0 =
      godementInvariantZeroPullback f hf := by
  rw [← cancel_mono (godementInvariantCompactCohomologyZeroIso X).hom]
  rw [godementInvariantCohomologyPullbackNatTrans_zero_toFunctions,
    godementInvariantZeroPullback_toFunctions]

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
