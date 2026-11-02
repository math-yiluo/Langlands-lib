import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactSupport
import Langlands.Sheaf.Equivariant.LocallyConstantSmoothCompactSupport
import Langlands.Cohomology.SmoothGodementCohomology

/-! # Smooth sheaf cohomology on actual induced rational spectra -/

noncomputable section

universe u

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

/-- The full ordinary-open locally constant smooth sheaf on the constructed
balanced quotient spectrum, with every original coefficient map. -/
def sheafFunctor :
    SmoothRep.{u, u, u} R G ⥤ SmoothTopologicalSheaf R G X.InducedSpectrum :=
  LocallyConstantSheaf.smoothFunctor R G X.InducedSpectrum

/-- All compact functions identify naturally with the actual compact sections
of the constructed smooth sheaf. -/
def compactSectionsIso :
    CompactSections.coefficientFunctor (R := R) X ≅
      sheafFunctor X ⋙ smoothSheafCompactSections R G X.InducedSpectrum :=
  LocallyConstantSheaf.CompactSections.smoothSheafComparison R G X.InducedSpectrum

/-- Compact sections of the smooth Godement complex of the full sheaf on the
actual induced spectrum. -/
def godementCompactComplex :
    SmoothRep.{u, u, u} R G ⥤ CochainComplex (SmoothRep.{u, u, u} R G) ℕ :=
  sheafFunctor X ⋙
    SmoothGodementCohomology.smoothGodementCompactComplex R G X.InducedSpectrum

/-- Cohomology of that constructed smooth Godement compact-section complex. -/
def godementCompactCohomology (q : ℕ) :
    SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G :=
  godementCompactComplex X ⋙
    HomologicalComplex.homologyFunctor (SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q

/-- In degree zero the actual smooth Godement cohomology is the full compact
function representation, naturally in all smooth coefficients. -/
def godementCompactCohomologyZeroIso :
    godementCompactCohomology (R := R) X 0 ≅ CompactSections.coefficientFunctor X :=
  Functor.isoWhiskerLeft (sheafFunctor X)
      (SmoothGodementCohomology.smoothGodementCompactCohomologyZeroIso
        R G X.InducedSpectrum) ≪≫
    (compactSectionsIso X).symm

/-- The right derived compact-section functor in the smooth sheaf category,
evaluated on the actual full locally constant sheaf. -/
def compactDerived (q : ℕ) :
    SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G :=
  sheafFunctor X ⋙ SmoothSheafCohomology.compactDerived R G X.InducedSpectrum q

/-- Degree-zero derived compact sections recover all compact functions on
the induced spectrum, including their diagonal action and coefficient maps. -/
def compactDerivedZeroIso :
    compactDerived (R := R) X 0 ≅ CompactSections.coefficientFunctor X :=
  Functor.isoWhiskerLeft (sheafFunctor X)
      (SmoothSheafCohomology.compactDerivedZeroIso R G X.InducedSpectrum) ≪≫
    (compactSectionsIso X).symm

/-- Any injective resolution of this constructed sheaf computes the genuine
derived compact sections. -/
def compactDerivedIso (M : SmoothRep.{u, u, u} R G)
    (I : InjectiveResolution ((sheafFunctor X).obj M)) (q : ℕ) :
    (compactDerived X q).obj M ≅
      (HomologicalComplex.homologyFunctor (SmoothRep.{u, u, u} R G)
        (ComplexShape.up ℕ) q).obj
        (((smoothSheafCompactSections R G X.InducedSpectrum).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) :=
  SmoothSheafCohomology.compactDerivedIso R G X.InducedSpectrum I q

/-- The two constructed routes agree in degree zero through their actual
identifications with the full compact-function functor. -/
def godementDerivedZeroIso :
    godementCompactCohomology (R := R) X 0 ≅ compactDerived X 0 :=
  godementCompactCohomologyZeroIso X ≪≫ (compactDerivedZeroIso X).symm

/-- The degree-zero comparison respects the full compact-function identification. -/
@[reassoc (attr := simp)]
theorem godementDerivedZeroIso_hom_comp :
    (godementDerivedZeroIso (R := R) X).hom ≫ (compactDerivedZeroIso X).hom =
      (godementCompactCohomologyZeroIso X).hom := by
  simp [godementDerivedZeroIso]

end OpenSubgroupTransport.SmoothCohomology

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
