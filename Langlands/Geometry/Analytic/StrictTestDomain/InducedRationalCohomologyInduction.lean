import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactInduction
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalDerivedComplex
import Langlands.Cohomology.SupercuspidalExt.Reciprocity

/-! # Compact induction and subgroup Ext for actual induced-spectrum cohomology -/

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

namespace OpenSubgroupTransport.CompactSections

variable (X : ρ.OpenSubgroupTransport)

/-- Every equivariant map from the full compact functions is determined by its
restriction along actual unit-chart zero extension. -/
def homSubgroupLinearEquiv (M W : SmoothRep.{u, u, u} R G) :
    ((coefficientFunctor X).obj M ⟶ W) ≃ₗ[R]
      ((localCoefficientFunctor X).obj M ⟶
        (SupercuspidalExt.restriction R G X.subgroup.toSubgroup).obj W) :=
  ((((linearCoyoneda R (SmoothRep.{u, u, u} R G)).mapIso
      ((compactInductionNatIso X).app M).symm.op).app W).toLinearEquiv).trans
    (SupercuspidalExt.homLinearEquiv R X.subgroup.isOpen'
      ((localCoefficientFunctor X).obj M) W)

/-- The coset-sum inverse sends the induction unit to actual unit-chart extension. -/
@[simp]
theorem fromCompactInduction_unitFunction (M : SmoothRep.{u, u, u} R G)
    (s : LocallyConstant X.LocalSpectrum M) :
    fromCompactInductionIntertwiner X M
        (Induction.unitFunction X.subgroup.toSubgroup X.subgroup.isOpen'
          (localRepresentation X M) (localRepresentation_isSmooth X M) s) =
      localChartExtension X 1 s := by
  apply toCompactInduction_injective X M
  rw [to_fromCompactInduction, toCompactInduction_localChartExtension]

/-- The Hom equivalence is literally restriction along unit-chart zero extension. -/
@[simp]
theorem homSubgroupLinearEquiv_apply (M W : SmoothRep.{u, u, u} R G)
    (T : (coefficientFunctor X).obj M ⟶ W) (s : LocallyConstant X.LocalSpectrum M) :
    SmoothRep.hom (homSubgroupLinearEquiv X M W T) s =
      SmoothRep.hom T (localChartExtension X 1 s) := by
  change SmoothRep.hom
      ((Induction.compactInductionAdjunction X.subgroup.toSubgroup X.subgroup.isOpen').homEquiv
        ((localCoefficientFunctor X).obj M) W ((compactInductionIso X M).inv ≫ T)) s = _
  rw [Induction.compactInductionAdjunction_homEquiv]
  change SmoothRep.hom T (fromCompactInductionIntertwiner X M
    (Induction.unitFunction X.subgroup.toSubgroup X.subgroup.isOpen'
      (localRepresentation X M) (localRepresentation_isSmooth X M) s)) = _
  rw [fromCompactInduction_unitFunction]

/-- The inverse evaluates the existing finite coset sum on the actual
geometric induction coordinates. -/
@[simp]
theorem homSubgroupLinearEquiv_symm_apply (M W : SmoothRep.{u, u, u} R G)
    (φ : (localCoefficientFunctor X).obj M ⟶
      (SupercuspidalExt.restriction R G X.subgroup.toSubgroup).obj W)
    (f : (coefficientFunctor X).obj M) :
    SmoothRep.hom ((homSubgroupLinearEquiv X M W).symm φ) f =
      Induction.cosetSum X.subgroup.toSubgroup X.subgroup.isOpen' W.representation
        (localRepresentation X M) (SmoothRep.hom φ) (toCompactInduction X M f) := by
  change SmoothRep.hom
      (((Induction.compactInductionAdjunction X.subgroup.toSubgroup X.subgroup.isOpen').homEquiv
        ((localCoefficientFunctor X).obj M) W).symm φ) (toCompactInduction X M f) = _
  rw [Induction.compactInductionAdjunction_homEquiv]
  rfl

/-- Restricting along the unit chart commutes with every smooth target map. -/
theorem homSubgroupLinearEquiv_naturality_target
    (M W W' : SmoothRep.{u, u, u} R G)
    (T : (coefficientFunctor X).obj M ⟶ W) (b : W ⟶ W') :
    homSubgroupLinearEquiv X M W' (T ≫ b) =
      homSubgroupLinearEquiv X M W T ≫
        (SupercuspidalExt.restriction R G X.subgroup.toSubgroup).map b := by
  ext s
  simp only [SmoothRep.hom_comp]
  rfl

/-- Unit-chart restriction and finite coset sum form a natural isomorphism
of equivariant Hom functors with values in the original coefficient modules. -/
def homSubgroupIso (M : SmoothRep.{u, u, u} R G) :
    SmoothHomComplex.homFunctor R G ((coefficientFunctor X).obj M) ≅
      SupercuspidalExt.restriction R G X.subgroup.toSubgroup ⋙
        SmoothHomComplex.homFunctor R X.subgroup.toSubgroup
          ((localCoefficientFunctor X).obj M) :=
  NatIso.ofComponents (fun W => (homSubgroupLinearEquiv X M W).toModuleIso)
    (fun {W W'} b => by
      ext T
      exact homSubgroupLinearEquiv_naturality_target X M W W' T b)

/-- Ext from the full original compact-function representation is subgroup Ext
from the full local-section representation, naturally in its smooth target. -/
def extSubgroupIso (M : SmoothRep.{u, u, u} R G) (n : ℕ) :
    SmoothExt.ext R G ((coefficientFunctor X).obj M) n ≅
      SupercuspidalExt.restriction R G X.subgroup.toSubgroup ⋙
        SmoothExt.ext R X.subgroup.toSubgroup ((localCoefficientFunctor X).obj M) n :=
  (SmoothExt.bifunctor R G n).mapIso ((compactInductionNatIso X).app M).symm.op ≪≫
    SupercuspidalExt.extCompactInductionIso R X.subgroup.isOpen'
      ((localCoefficientFunctor X).obj M) n

end OpenSubgroupTransport.CompactSections

namespace OpenSubgroupTransport.SmoothCohomology

variable (X : ρ.OpenSubgroupTransport) [HasStableNeighbourhoods G X.InducedSpectrum]

/-- Compact sections of the full smooth sheaf are compact induction of all
local-spectrum sections, including the original coefficient maps. -/
def sheafCompactSectionsInductionIso :
    sheafFunctor (R := R) X ⋙ smoothSheafCompactSections R G X.InducedSpectrum ≅
      CompactSections.compactInducedCoefficientFunctor X :=
  (compactSectionsIso X).symm ≪≫ CompactSections.compactInductionNatIso X

/-- The degree-zero smooth Godement cohomology of the actual sheaf is the
compact induction of its full local-spectrum coefficient representation. -/
def godementZeroInductionIso :
    godementCompactCohomology (R := R) X 0 ≅
      CompactSections.compactInducedCoefficientFunctor X :=
  godementCompactCohomologyZeroIso X ≪≫ CompactSections.compactInductionNatIso X

/-- Genuine sheaf-derived compact sections in degree zero are the same full
compact induction, naturally in every coefficient intertwiner. -/
def derivedZeroInductionIso :
    compactDerived (R := R) X 0 ≅ CompactSections.compactInducedCoefficientFunctor X :=
  compactDerivedZeroIso X ≪≫ CompactSections.compactInductionNatIso X

/-- The existing degree-zero route comparison respects compact induction. -/
@[reassoc (attr := simp)]
theorem godementDerivedZeroIso_hom_comp_derivedZeroInductionIso :
    (godementDerivedZeroIso (R := R) X).hom ≫ (derivedZeroInductionIso X).hom =
      (godementZeroInductionIso X).hom := by
  simp [derivedZeroInductionIso, godementZeroInductionIso, godementDerivedZeroIso]

/-- All Ext degrees from the actual degree-zero derived compact sections are
subgroup Ext from all original local-spectrum sections. -/
def derivedZeroExtSubgroupIso (M : SmoothRep.{u, u, u} R G) (n : ℕ) :
    SmoothExt.ext R G ((compactDerived X 0).obj M) n ≅
      SupercuspidalExt.restriction R G X.subgroup.toSubgroup ⋙
        SmoothExt.ext R X.subgroup.toSubgroup
          ((CompactSections.localCoefficientFunctor X).obj M) n :=
  (SmoothExt.bifunctor R G n).mapIso ((compactDerivedZeroIso X).app M).symm.op ≪≫
    CompactSections.extSubgroupIso X M n

section DerivedComplex

variable [HasDerivedCategory.{w} (SmoothTopologicalSheaf R G X.InducedSpectrum)]
  [HasDerivedCategory.{w'} (SmoothRep.{u, u, u} R G)]

/-- Degree-zero homology of the actual bounded-below derived compact complex
identifies naturally with the full compact-induction functor. -/
def derivedComplexZeroInductionIso :
    compactDerivedComplex (R := R) X ⋙
        DerivedCategory.Plus.homologyFunctor (SmoothRep.{u, u, u} R G) 0 ≅
      CompactSections.compactInducedCoefficientFunctor X :=
  compactDerivedComplexHomologyZeroIso X ≪≫ CompactSections.compactInductionNatIso X

/-- The derived-complex identification agrees with degree-zero sheaf-derived
compact sections under the constructed natural cohomology comparison. -/
@[reassoc (attr := simp)]
theorem compactDerivedComplexHomologyIso_hom_comp_derivedZeroInductionIso :
    (compactDerivedComplexHomologyIso (R := R) X 0).hom ≫
        (derivedZeroInductionIso X).hom = (derivedComplexZeroInductionIso X).hom := by
  simp [derivedZeroInductionIso, derivedComplexZeroInductionIso,
    compactDerivedComplexHomologyZeroIso]

/-- The zero row on page two of the actual compact hyperext spectral sequence
is subgroup Ext from every original local-spectrum section. -/
def compactHyperextZeroRowSubgroupAddEquiv
    (M W : SmoothRep.{u, u, u} R G) (p : ℕ) :
    ((compactHyperextSpectralSequence X M W).page 2).X ⟨p, 0⟩ ≃+
      (SmoothExt.ext R X.subgroup.toSubgroup
        ((CompactSections.localCoefficientFunctor X).obj M) p).obj
          ((SupercuspidalExt.restriction R G X.subgroup.toSubgroup).obj W) :=
  (compactHyperextSecondPageZeroRowAddEquiv X M W p).trans
    ((CompactSections.extSubgroupIso X M p).app W).toLinearEquiv.toAddEquiv

/-- The origin on page two is the module of genuine subgroup-equivariant maps
from all local-spectrum sections to the restricted smooth target. -/
def compactHyperextOriginSubgroupHomAddEquiv
    (M W : SmoothRep.{u, u, u} R G) :
    ((compactHyperextSpectralSequence X M W).page 2).X ⟨0, 0⟩ ≃+
      ((CompactSections.localCoefficientFunctor X).obj M ⟶
        (SupercuspidalExt.restriction R G X.subgroup.toSubgroup).obj W) :=
  (compactHyperextZeroRowSubgroupAddEquiv X M W 0).trans
    ((SmoothExt.extZeroIso R X.subgroup.toSubgroup
      ((CompactSections.localCoefficientFunctor X).obj M)).app
        ((SupercuspidalExt.restriction R G X.subgroup.toSubgroup).obj W)).toLinearEquiv.toAddEquiv

end DerivedComplex

end OpenSubgroupTransport.SmoothCohomology

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
