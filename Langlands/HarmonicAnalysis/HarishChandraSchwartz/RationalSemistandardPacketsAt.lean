import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitPacketContinuation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardDynamicNormalization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardCompactAt
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceQuotientHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardComparisonHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacketPairing
import Langlands.Representation.Plancherel.ActualOppositeFullDomainContinuationProof

/-! # Actual semistandard packet data at a common compact -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.GroupScheme Langlands.Plancherel
open Langlands.BruhatTits.Iwasawa Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G)
  {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]
  (rs : ∀ p : SemistandardSpectralIndex i, CocharacterPresentation hG p)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (products : DynamicParabolicProducts K.toSubgroup)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
/-- Construct the opposite scalar data for every actual orbit at the
specified compact and with the intrinsic quotient Haar. -/
def packetsAtCompact (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    OrbitPacketData (rs t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2) := by
  let m := chosenLeviModel t.1
  let π := orbitRepresentative m (a t.1) (ha t.1) (mu t.1) t.2
  have hsq := orbitRepresentative_isSquareIntegrable m (a t.1) (ha t.1) (mu t.1) t.2
  let normalization := (rs t.1).leviNormalization m (a t.1) (ha t.1) (mu t.1) π hsq
  exact OrbitPacketData.conditionalOfFullDomainContinuation (rs t.1) π K hK products
    normalization actualOppositeFullDomainContinuation.{u, uV}

set_option maxRecDepth 4096 in
@[simp] theorem packetsAtCompact_compact (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    (packetsAtCompact hG a ha mu rs K hK products t).compact = K := rfl

variable (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
  (hν : IsGenericCocharacter i ν)
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option maxRecDepth 4096 in
/-- The coefficient compact pictures and all the selected scalar data use
the same prescribed special compact. -/
theorem packetsAtCompact_sourceCompactCompatibility
    (hSpecial : SpecialCompactProperties F i ν K.toSubgroup) :
    WavePacketPairing.SourceCompactCompatibility hG a ha mu
      (CompactData.atMinimalIwasawa hG hi hν hK hPK) rs
      (packetsAtCompact hG a ha mu rs K hK products) (nu := ν) (K := K) :=
  ⟨hSpecial, fun _ => rfl, fun _ => rfl⟩

omit [∀ p, (mu p).IsHaarMeasure] in
/-- The normalized quotient Haar used with these compact pictures is the
Haar of the exact same compact trace. -/
theorem sourceQuotientHaar_intrinsicNormalization :
    SourceMeasure.IntrinsicQuotientNormalization a
      (fun p => (chosenLeviModel p).sourceQuotientHaar (a p) K hK)
      (CompactData.atMinimalIwasawa hG hi hν hK hPK) :=
  fun p => (chosenLeviModel p).sourceQuotientHaar_normalized (a p) K hK

end Langlands.HarishChandraSchwartz.RationalSemistandard
