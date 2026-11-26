import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProjectionContinuityProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacket

/-! # The modular character of each actual semistandard parabolic -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

/-- For every intrinsic semistandard index of a connected reductive group with a
maximal split torus, the modular character of the rational points of the parabolic
is the Haar modulus of conjugation on its radical. The Levi and the radical are
unimodular, and the semidirect-product formula applies to them. -/
theorem rationalSemistandardModularNormalization
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} :
    RationalSemistandardModularNormalizationStatement (F := F) (S := S) (G := G) (i := i) := by
  intro hG hi p x
  let r := RationalSemistandard.CocharacterPresentation.ofCoverage hG
    semistandardSpectralDynamicCoverage hi p
  let : LocallyCompactSpace (RationalSemistandard.levi p) :=
    (RationalSemistandard.isClosed_levi_of_model
      (RationalSemistandard.chosenLeviModel p)).locallyCompactSpace
  let : LocallyCompactSpace (RationalSemistandard.parabolic p) :=
    (RationalSemistandard.isClosed_parabolic p).locallyCompactSpace
  let : LocallyCompactSpace (RationalSemistandard.radical p) :=
    (RationalSemistandard.isClosed_radical p).locallyCompactSpace
  simpa only [Langlands.HaarModulus.closedRestrictCharacter_eq] using
    (RationalSemistandard.decomposition p).modularCharacter_eq_restrictCharacter_of_unimodular
      (RationalSemistandard.projectionContinuity inferInstance hG hi p)
      (RationalSemistandard.levi_modularCharacter (RationalSemistandard.chosenLeviModel p))
      (RationalSemistandard.radical_isUnimodular hG r) x

end Langlands.HarishChandraSchwartz
