import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitStatement
import Langlands.FieldTheory.HenselianDiscreteDimensionLEOneProof
import Langlands.GroupScheme.Rational.SteinbergAssembly
import Langlands.GroupScheme.Rational.DimensionLEOneTorusCocycleVanishingProof
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceReduction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Adjoint.ExistenceProof
import Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReduction
import Langlands.GroupScheme.SimplyConnected.CoverExistenceProof
import Langlands.GroupScheme.Rational.InfiniteFieldStronglyRegularPoint
import Langlands.GroupScheme.Rational.QuasiSplitRegularConjugateReduction
import Langlands.GroupScheme.Rational.RegularConjugateFiniteGaloisProof

/-! # Henselian discrete quasi-splitness from rational strongly regular classes -/

universe u

namespace Langlands.GroupScheme

/-- Quasi-splitness over Henselian discretely valued fields with algebraically closed residue
follows from the rationality of Galois-stable strongly regular classes in simply connected
quasi-split groups. -/
def HenselianDiscreteQuasiSplitReductionStatement : Prop :=
  QuasiSplitRegularClassRationalStatement.{u} → HenselianDiscreteQuasiSplitStatement.{u}

/-- Steinberg's theorem over fields of dimension at most one follows from the rationality of
Galois-stable strongly regular classes. -/
theorem dimensionLEOneQuasiSplit_of_classRational
    (h : QuasiSplitRegularClassRationalStatement.{u}) :
    DimensionLEOneQuasiSplitStatement.{u} :=
  dimensionLEOneQuasiSplit_of_structural_inputs
    (quasiSplitInnerFormExistence_of_rootDatum_adjoint rootDatumExistence
      adjointQuotientExistence)
    (quasiSplitCocycleTorusReduction_of_prerequisites simplyConnectedCoverExistence
      infiniteFieldStronglyRegularPoint
      (quasiSplitSimplyConnectedRegularConjugate_of_classRational h
        regularConjugateFiniteGalois))
    dimensionLEOneTorusCocycleVanishing

/-- Steinberg's theorem over fields of dimension at most one gives quasi-splitness over
Henselian discretely valued fields with algebraically closed residue. -/
theorem henselianDiscreteQuasiSplit_of_dimensionLEOne
    (h : DimensionLEOneQuasiSplitStatement.{u}) :
    HenselianDiscreteQuasiSplitStatement.{u} := by
  intro K _ v hv hH hres G hG
  exact h K (Langlands.FieldTheory.henselianDiscreteDimensionLEOne K v hv hH hres) G hG

/-- The reduction of Henselian discrete quasi-splitness to rational strongly regular classes. -/
theorem henselianDiscreteQuasiSplitReduction :
    HenselianDiscreteQuasiSplitReductionStatement.{u} := fun h =>
  henselianDiscreteQuasiSplit_of_dimensionLEOne (dimensionLEOneQuasiSplit_of_classRational h)

end Langlands.GroupScheme
