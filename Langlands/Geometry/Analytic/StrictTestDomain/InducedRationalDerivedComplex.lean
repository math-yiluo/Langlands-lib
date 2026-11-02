import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothCohomology
import Langlands.Cohomology.SmoothSheafDerivedComplex
import Langlands.Cohomology.DerivedPlusNaturality
import Langlands.Cohomology.SmoothHyperextSecondPage

/-! # Derived compact complexes and hyperext on actual induced rational spectra -/

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
  [HasDerivedCategory.{w} (SmoothTopologicalSheaf R G X.InducedSpectrum)]
  [HasDerivedCategory.{w'} (SmoothRep.{u, u, u} R G)]

/-- Derived compact sections of the full locally constant sheaf on the actual
balanced quotient spectrum, as a bounded below derived smooth representation. -/
def compactDerivedComplex :
    SmoothRep.{u, u, u} R G ⥤ DerivedCategory.Plus (SmoothRep.{u, u, u} R G) :=
  sheafFunctor X ⋙ SmoothSheafDerivedComplex.compactComplex R G X.InducedSpectrum

/-- Its cohomology is naturally the existing sheaf-derived compact sections,
including the original coefficient maps. -/
def compactDerivedComplexHomologyIso (q : ℕ) :
    compactDerivedComplex (R := R) X ⋙
        DerivedCategory.Plus.homologyFunctor (SmoothRep.{u, u, u} R G) q ≅
      compactDerived X q :=
  Functor.isoWhiskerLeft (sheafFunctor X)
    (DerivedPlus.homologyNatIso (smoothSheafCompactSections R G X.InducedSpectrum) q)

/-- The actual derived complex is represented by compact sections of any
injective resolution of the constructed sheaf. -/
def compactDerivedComplexIso (M : SmoothRep.{u, u, u} R G)
    (I : InjectiveResolution ((sheafFunctor X).obj M)) :
    (compactDerivedComplex X).obj M ≅ DerivedCategory.Plus.Q.obj
      ((smoothSheafCompactSections R G X.InducedSpectrum).mapCochainComplexPlus.obj
        (DerivedPlus.resolutionPlus I)) :=
  DerivedPlus.derivedComplexIso (smoothSheafCompactSections R G X.InducedSpectrum) I

/-- The natural cohomology comparison can be computed with any such resolution. -/
theorem compactDerivedComplexHomologyIso_hom_app (M : SmoothRep.{u, u, u} R G)
    (I : InjectiveResolution ((sheafFunctor X).obj M)) (q : ℕ) :
    (compactDerivedComplexHomologyIso X q).hom.app M =
      (DerivedPlus.homologyIso (smoothSheafCompactSections R G X.InducedSpectrum) I q).hom :=
  DerivedPlus.homologyNatIso_hom_app _ q I

/-- Negative cohomology of this constructed derived complex vanishes. -/
theorem isZero_compactDerivedComplex_homology (M : SmoothRep.{u, u, u} R G)
    {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (SmoothRep.{u, u, u} R G) n).obj
      ((compactDerivedComplex X).obj M)) :=
  SmoothSheafDerivedComplex.isZero_compactComplex_homology R G X.InducedSpectrum
    ((sheafFunctor X).obj M) hn

/-- Degree-zero cohomology is the full compact-function representation with
its original diagonal action, naturally in every coefficient intertwiner. -/
def compactDerivedComplexHomologyZeroIso :
    compactDerivedComplex (R := R) X ⋙
        DerivedCategory.Plus.homologyFunctor (SmoothRep.{u, u, u} R G) 0 ≅
      CompactSections.coefficientFunctor X :=
  compactDerivedComplexHomologyIso X 0 ≪≫ compactDerivedZeroIso X

/-- The same actual derived compact complex in the unbounded derived category,
for use by the standard-t-structure hyperext construction. -/
def compactDerivedObject :
    SmoothRep.{u, u, u} R G ⥤ DerivedCategory (SmoothRep.{u, u, u} R G) :=
  compactDerivedComplex X ⋙ DerivedCategory.Plus.ι

/-- The cohomology identification also holds after the derived inclusion. -/
def compactDerivedObjectHomologyIso (q : ℕ) :
    compactDerivedObject (R := R) X ⋙
        DerivedCategory.homologyFunctor (SmoothRep.{u, u, u} R G) q ≅
      compactDerived X q :=
  compactDerivedComplexHomologyIso X q

/-- The actual hyperext spectral sequence for derived compact sections of the
constructed sheaf and a smooth target representation placed in degree zero. -/
def compactHyperextSpectralSequence (M W : SmoothRep.{u, u, u} R G) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{w'} :=
  HyperextSpectralSequence.hyperextSpectralSequence DerivedCategory.TStructure.t
    ((compactDerivedObject X).obj M)
    ((DerivedCategory.singleFunctor (SmoothRep.{u, u, u} R G) 0).obj W)

/-- Position `(p,-q)` on page two is smooth Ext from the actual degree-q
sheaf-derived compact sections, for nonnegative integers p and q. -/
def compactHyperextSecondPageAddEquiv (M W : SmoothRep.{u, u, u} R G) (p q : ℕ) :
    ((compactHyperextSpectralSequence X M W).page 2).X ⟨p, -(q : ℤ)⟩ ≃+
      (SmoothExt.ext R G ((compactDerived X q).obj M) p).obj W := by
  have e :
      ((compactHyperextSpectralSequence X M W).page 2).X ⟨p, -(q : ℤ)⟩ ≃+
        (SmoothExt.ext R G
          ((DerivedCategory.homologyFunctor (SmoothRep.{u, u, u} R G) q).obj
            ((compactDerivedObject X).obj M)) p).obj W := by
    have h := SmoothHyperext.secondPageAddEquiv R G
      ((compactDerivedObject X).obj M) W p (-(q : ℤ))
    rw [neg_neg] at h
    exact h
  exact e.trans
    (((SmoothExt.bifunctor R G p).mapIso
      ((compactDerivedObjectHomologyIso X q).app M).symm.op).app W).toLinearEquiv.toAddEquiv

/-- The zero row is smooth Ext from the original full compact functions,
with no change to the coefficient representation. -/
def compactHyperextSecondPageZeroRowAddEquiv (M W : SmoothRep.{u, u, u} R G) (p : ℕ) :
    ((compactHyperextSpectralSequence X M W).page 2).X ⟨p, 0⟩ ≃+
      (SmoothExt.ext R G ((CompactSections.coefficientFunctor X).obj M) p).obj W :=
  (compactHyperextSecondPageAddEquiv X M W p 0).trans
    (((SmoothExt.bifunctor R G p).mapIso
      ((compactDerivedZeroIso X).app M).symm.op).app W).toLinearEquiv.toAddEquiv

/-- The zero column is the group of actual equivariant maps from the
sheaf-derived compact sections to the target. -/
def compactHyperextSecondPageZeroColumnAddEquiv
    (M W : SmoothRep.{u, u, u} R G) (q : ℕ) :
    ((compactHyperextSpectralSequence X M W).page 2).X ⟨0, -(q : ℤ)⟩ ≃+
      ((compactDerived X q).obj M ⟶ W) :=
  (compactHyperextSecondPageAddEquiv X M W 0 q).trans
    ((SmoothExt.extZeroIso R G ((compactDerived X q).obj M)).app W).toLinearEquiv.toAddEquiv

end OpenSubgroupTransport.SmoothCohomology

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
