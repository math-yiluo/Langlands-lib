import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothCohomology
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactComplex

/-! # Proper transport of degree-zero smooth cohomology on actual rational spectra -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Langlands.Sheaf.Equivariant

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type u} [CommRing R]

namespace OpenSubgroupTransport.Hom

open SmoothCohomology

variable {X Y Z : ρ.OpenSubgroupTransport}
  [HasStableNeighbourhoods G X.InducedSpectrum]
  [HasStableNeighbourhoods G Y.InducedSpectrum]
  [HasStableNeighbourhoods G Z.InducedSpectrum]

/-- Proper induced transport pullback on the actual degree-zero Godement objects.
It is defined by their proved identification with full compact functions. -/
def godementZeroPullback (f : X ⟶ Y) (hf : IsProperMap f.inducedMap) :
    godementCompactCohomology (R := R) Y 0 ⟶ godementCompactCohomology X 0 :=
  (godementCompactCohomologyZeroIso Y).hom ≫ compactSupportPullbackNatTrans f hf ≫
    (godementCompactCohomologyZeroIso X).inv

/-- Proper induced transport pullback on actual degree-zero derived compact sections.
No higher derived pullback is assumed by this definition. -/
def compactDerivedZeroPullback (f : X ⟶ Y) (hf : IsProperMap f.inducedMap) :
    compactDerived (R := R) Y 0 ⟶ compactDerived X 0 :=
  (compactDerivedZeroIso Y).hom ≫ compactSupportPullbackNatTrans f hf ≫
    (compactDerivedZeroIso X).inv

@[reassoc (attr := simp)]
theorem godementZeroPullback_toFunctions (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    godementZeroPullback (R := R) f hf ≫ (godementCompactCohomologyZeroIso X).hom =
      (godementCompactCohomologyZeroIso Y).hom ≫
        compactSupportPullbackNatTrans f hf := by
  simp [godementZeroPullback, Category.assoc]

@[reassoc (attr := simp)]
theorem compactDerivedZeroPullback_toFunctions (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    compactDerivedZeroPullback (R := R) f hf ≫ (compactDerivedZeroIso X).hom =
      (compactDerivedZeroIso Y).hom ≫ compactSupportPullbackNatTrans f hf := by
  simp [compactDerivedZeroPullback, Category.assoc]

/-- After the actual zero identification, the transported map is precomposition
with the constructed map of balanced quotient spectra. -/
@[simp]
theorem godementZeroPullback_apply (f : X ⟶ Y) (hf : IsProperMap f.inducedMap)
    (M : SmoothRep.{u, u, u} R G) (s : (godementCompactCohomology Y 0).obj M)
    (z : X.InducedSpectrum) :
    (SmoothRep.hom ((godementCompactCohomologyZeroIso X).hom.app M)
        (SmoothRep.hom ((godementZeroPullback f hf).app M) s)).val z =
      (SmoothRep.hom ((godementCompactCohomologyZeroIso Y).hom.app M) s).val
        (f.inducedMap z) := by
  have h := congrArg (fun b => SmoothRep.hom (b.app M) s)
    (godementZeroPullback_toFunctions (R := R) f hf)
  exact congrArg (fun t => t.val z) h

@[simp]
theorem compactDerivedZeroPullback_apply (f : X ⟶ Y) (hf : IsProperMap f.inducedMap)
    (M : SmoothRep.{u, u, u} R G) (s : (compactDerived Y 0).obj M)
    (z : X.InducedSpectrum) :
    (SmoothRep.hom ((compactDerivedZeroIso X).hom.app M)
        (SmoothRep.hom ((compactDerivedZeroPullback f hf).app M) s)).val z =
      (SmoothRep.hom ((compactDerivedZeroIso Y).hom.app M) s).val
        (f.inducedMap z) := by
  have h := congrArg (fun b => SmoothRep.hom (b.app M) s)
    (compactDerivedZeroPullback_toFunctions (R := R) f hf)
  exact congrArg (fun t => t.val z) h

@[simp]
theorem godementZeroPullback_id :
    godementZeroPullback (R := R) (𝟙 X) (isProperMap_inducedMap_id X) =
      𝟙 (godementCompactCohomology X 0) := by
  simp [godementZeroPullback]

@[simp]
theorem compactDerivedZeroPullback_id :
    compactDerivedZeroPullback (R := R) (𝟙 X) (isProperMap_inducedMap_id X) =
      𝟙 (compactDerived X 0) := by
  simp [compactDerivedZeroPullback]

/-- Pullback is contravariantly compatible with composition of proper transport. -/
theorem godementZeroPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) :
    godementZeroPullback (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) =
      godementZeroPullback g hg ≫ godementZeroPullback f hf := by
  simp [godementZeroPullback, compactSupportPullbackNatTrans_comp f g hf hg, Category.assoc,
    ← Category.assoc (godementCompactCohomologyZeroIso Y).inv
      (godementCompactCohomologyZeroIso Y).hom]

theorem compactDerivedZeroPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) :
    compactDerivedZeroPullback (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) =
      compactDerivedZeroPullback g hg ≫ compactDerivedZeroPullback f hf := by
  simp [compactDerivedZeroPullback, compactSupportPullbackNatTrans_comp f g hf hg, Category.assoc,
    ← Category.assoc (compactDerivedZeroIso Y).inv (compactDerivedZeroIso Y).hom]

/-- The original degree-zero Godement/derived comparison commutes with every
proper induced transport pullback. -/
@[reassoc (attr := simp)]
theorem godementDerivedZeroIso_pullback (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    godementZeroPullback (R := R) f hf ≫ (godementDerivedZeroIso X).hom =
      (godementDerivedZeroIso Y).hom ≫ compactDerivedZeroPullback f hf := by
  simp [godementZeroPullback, compactDerivedZeroPullback, godementDerivedZeroIso,
    Category.assoc,
    ← Category.assoc (godementCompactCohomologyZeroIso X).inv
      (godementCompactCohomologyZeroIso X).hom,
    ← Category.assoc (compactDerivedZeroIso Y).inv (compactDerivedZeroIso Y).hom]

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
