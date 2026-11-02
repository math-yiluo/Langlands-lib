import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothCohomology
import Langlands.Cohomology.SmoothSheafDerivedComplex
import Langlands.Cohomology.DerivedPlusNaturality
import Langlands.Cohomology.SmoothGodementComparison.Invariants

/-! # Invariant compact complexes on actual induced rational spectra -/

noncomputable section

universe u w w'

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant
open Langlands.Cohomology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type u} [CommRing R]

namespace OpenSubgroupTransport.SmoothCohomology

variable (X : ρ.OpenSubgroupTransport) [HasStableNeighbourhoods G X.InducedSpectrum]

/-- The invariants of the original full compact-function representation,
with the original coefficient maps. -/
def invariantCompactFunctions : SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R :=
  CompactSections.coefficientFunctor X ⋙ SmoothGodementComparison.smoothInvariants R G

/-- All invariant compact functions identify naturally with the invariant
compact sections of the constructed full locally constant smooth sheaf. -/
def invariantCompactSectionsIso :
    invariantCompactFunctions (R := R) X ≅
      sheafFunctor X ⋙ SmoothSheafCohomology.invariantCompactSections R G X.InducedSpectrum :=
  Functor.isoWhiskerRight (compactSectionsIso X)
    (SmoothGodementComparison.smoothInvariants R G)

/-- Invariant compact sections applied termwise to the actual smooth
Godement complex of the constructed coefficient sheaf. -/
def godementInvariantCompactComplex :
    SmoothRep.{u, u, u} R G ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  sheafFunctor X ⋙
    SmoothGodementCohomology.smoothGodementInvariantCompactComplex R G X.InducedSpectrum

/-- Actual homology of that complex of invariant compact sections. -/
def godementInvariantCompactCohomology (q : ℕ) :
    SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R :=
  godementInvariantCompactComplex X ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q

/-- Degree-zero Godement invariant compact cohomology recovers all invariant
compact functions, naturally in the original smooth coefficient module. -/
def godementInvariantCompactCohomologyZeroIso :
    godementInvariantCompactCohomology (R := R) X 0 ≅ invariantCompactFunctions X :=
  Functor.isoWhiskerLeft (sheafFunctor X)
      (SmoothGodementCohomology.smoothGodementInvariantCompactCohomologyZeroIso
        R G X.InducedSpectrum) ≪≫
    (invariantCompactSectionsIso X).symm

/-- Derived invariant compact sections in the smooth sheaf category,
evaluated on the actual full locally constant coefficient sheaf. -/
def invariantCompactDerived (q : ℕ) :
    SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R :=
  sheafFunctor X ⋙ SmoothSheafCohomology.invariantCompactDerived R G X.InducedSpectrum q

/-- In degree zero these sheaf-derived invariant sections recover the
invariants of all original compact functions. -/
def invariantCompactDerivedZeroIso :
    invariantCompactDerived (R := R) X 0 ≅ invariantCompactFunctions X :=
  Functor.isoWhiskerLeft (sheafFunctor X)
      (SmoothSheafCohomology.invariantCompactDerivedZeroIso R G X.InducedSpectrum) ≪≫
    (invariantCompactSectionsIso X).symm

/-- Any injective resolution of the constructed sheaf computes its actual
derived invariant compact sections. -/
def invariantCompactDerivedIso (M : SmoothRep.{u, u, u} R G)
    (I : InjectiveResolution ((sheafFunctor X).obj M)) (q : ℕ) :
    (invariantCompactDerived X q).obj M ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).obj
        (((SmoothSheafCohomology.invariantCompactSections R G X.InducedSpectrum).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) :=
  SmoothSheafCohomology.invariantCompactDerivedIso R G X.InducedSpectrum I q

/-- The Godement and sheaf-derived invariant constructions agree in degree
zero through their full compact-function identifications. -/
def godementInvariantDerivedZeroIso :
    godementInvariantCompactCohomology (R := R) X 0 ≅ invariantCompactDerived X 0 :=
  godementInvariantCompactCohomologyZeroIso X ≪≫ (invariantCompactDerivedZeroIso X).symm

/-- This degree-zero route comparison preserves the full compact functions. -/
@[reassoc (attr := simp)]
theorem godementInvariantDerivedZeroIso_hom_comp :
    (godementInvariantDerivedZeroIso (R := R) X).hom ≫
        (invariantCompactDerivedZeroIso X).hom =
      (godementInvariantCompactCohomologyZeroIso X).hom := by
  simp [godementInvariantDerivedZeroIso]

/-- The canonical map from homology of termwise invariants to invariants of
the actual compact Godement cohomology. -/
def godementInvariantsEdge (q : ℕ) :
    godementInvariantCompactCohomology (R := R) X q ⟶
      godementCompactCohomology X q ⋙ SmoothGodementComparison.smoothInvariants R G :=
  Functor.whiskerLeft (sheafFunctor X)
    (SmoothGodementComparison.godementEdge (X := X.InducedSpectrum)
      (SmoothGodementComparison.smoothInvariants R G) q)

/-- The canonical map from sheaf-derived invariant compact sections to the
invariants of actual sheaf-derived compact sections. -/
def derivedInvariantsEdge (q : ℕ) :
    invariantCompactDerived (R := R) X q ⟶
      compactDerived X q ⋙ SmoothGodementComparison.smoothInvariants R G :=
  Functor.whiskerLeft (sheafFunctor X)
    (SmoothGodementComparison.derivedEdge (X := X.InducedSpectrum)
      (SmoothGodementComparison.smoothInvariants R G) q)

/-- The derived edge component is computed with any injective resolution of
the constructed coefficient sheaf. -/
theorem derivedInvariantsEdge_app (M : SmoothRep.{u, u, u} R G)
    (I : InjectiveResolution ((sheafFunctor X).obj M)) (q : ℕ) :
    (derivedInvariantsEdge X q).app M =
      LeftExactHomology.derivedHom (SmoothGodementComparison.smoothInvariants R G)
        (smoothSheafCompactSections R G X.InducedSpectrum) I q :=
  LeftExactHomology.derivedNatTrans_app _ _ I q

instance isIso_godementInvariantsEdge_zero : IsIso (godementInvariantsEdge (R := R) X 0) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

instance isIso_derivedInvariantsEdge_zero : IsIso (derivedInvariantsEdge (R := R) X 0) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

/-- Exact invariants give isomorphisms in every Godement degree; preservation
of homology remains an explicit hypothesis. -/
instance isIso_godementInvariantsEdge
    [(SmoothGodementComparison.smoothInvariants R G).PreservesHomology] (q : ℕ) :
    IsIso (godementInvariantsEdge (R := R) X q) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

/-- The corresponding derived edge is an isomorphism when invariants
preserve homology. -/
instance isIso_derivedInvariantsEdge
    [(SmoothGodementComparison.smoothInvariants R G).PreservesHomology] (q : ℕ) :
    IsIso (derivedInvariantsEdge (R := R) X q) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

section DerivedComplex

variable [HasDerivedCategory.{w} (SmoothTopologicalSheaf R G X.InducedSpectrum)]
  [HasDerivedCategory.{w'} (ModuleCat.{u} R)]

/-- The actual derived invariant compact-section complex of the full
coefficient sheaf, in the bounded-below derived category of modules. -/
def invariantCompactDerivedComplex :
    SmoothRep.{u, u, u} R G ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  sheafFunctor X ⋙ SmoothSheafDerivedComplex.invariantCompactComplex R G X.InducedSpectrum

/-- Its homology is naturally the existing sheaf-derived invariant compact
sections, for every original coefficient intertwiner. -/
def invariantCompactDerivedComplexHomologyIso (q : ℕ) :
    invariantCompactDerivedComplex (R := R) X ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q ≅
      invariantCompactDerived X q :=
  Functor.isoWhiskerLeft (sheafFunctor X)
    (DerivedPlus.homologyNatIso
      (SmoothSheafCohomology.invariantCompactSections R G X.InducedSpectrum) q)

/-- Any injective resolution represents this actual derived complex. -/
def invariantCompactDerivedComplexIso (M : SmoothRep.{u, u, u} R G)
    (I : InjectiveResolution ((sheafFunctor X).obj M)) :
    (invariantCompactDerivedComplex X).obj M ≅ DerivedCategory.Plus.Q.obj
      ((SmoothSheafCohomology.invariantCompactSections R G X.InducedSpectrum).mapCochainComplexPlus.obj
        (DerivedPlus.resolutionPlus I)) :=
  DerivedPlus.derivedComplexIso
    (SmoothSheafCohomology.invariantCompactSections R G X.InducedSpectrum) I

/-- The natural homology comparison agrees with computation using every
injective resolution of the constructed coefficient sheaf. -/
theorem invariantCompactDerivedComplexHomologyIso_hom_app
    (M : SmoothRep.{u, u, u} R G)
    (I : InjectiveResolution ((sheafFunctor X).obj M)) (q : ℕ) :
    (invariantCompactDerivedComplexHomologyIso X q).hom.app M =
      (DerivedPlus.homologyIso
        (SmoothSheafCohomology.invariantCompactSections R G X.InducedSpectrum) I q).hom :=
  DerivedPlus.homologyNatIso_hom_app _ q I

/-- Negative homology of the constructed invariant derived complex vanishes. -/
theorem isZero_invariantCompactDerivedComplex_homology (M : SmoothRep.{u, u, u} R G)
    {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).obj
      ((invariantCompactDerivedComplex X).obj M)) :=
  SmoothSheafDerivedComplex.isZero_invariantCompactComplex_homology
    R G X.InducedSpectrum ((sheafFunctor X).obj M) hn

/-- Degree-zero homology is naturally the invariants of the original full
compact-function representation. -/
def invariantCompactDerivedComplexHomologyZeroIso :
    invariantCompactDerivedComplex (R := R) X ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0 ≅
      invariantCompactFunctions X :=
  invariantCompactDerivedComplexHomologyIso X 0 ≪≫ invariantCompactDerivedZeroIso X

/-- The natural map from homology of the invariant derived complex to
invariants of the actual compact cohomology. -/
def invariantCompactDerivedComplexEdge (q : ℕ) :
    invariantCompactDerivedComplex (R := R) X ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q ⟶
      compactDerived X q ⋙ SmoothGodementComparison.smoothInvariants R G :=
  (invariantCompactDerivedComplexHomologyIso X q).hom ≫ derivedInvariantsEdge X q

instance isIso_invariantCompactDerivedComplexEdge_zero :
    IsIso (invariantCompactDerivedComplexEdge (R := R) X 0) := by
  dsimp [invariantCompactDerivedComplexEdge]
  infer_instance

instance isIso_invariantCompactDerivedComplexEdge
    [(SmoothGodementComparison.smoothInvariants R G).PreservesHomology] (q : ℕ) :
    IsIso (invariantCompactDerivedComplexEdge (R := R) X q) := by
  dsimp [invariantCompactDerivedComplexEdge]
  infer_instance

end DerivedComplex

end OpenSubgroupTransport.SmoothCohomology

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
