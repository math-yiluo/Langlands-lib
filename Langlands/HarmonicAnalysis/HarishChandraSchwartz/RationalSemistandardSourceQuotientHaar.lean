import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaFixed
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralSubgroupQuotientHaar
import Langlands.Representation.Plancherel.WaldspurgerSourceNormalization

/-! # Source quotient Haar at the literal semistandard compact trace -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel.WaldspurgerSourceNormalization

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.LeviModel

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} (m : LeviModel p)
  {Z : CommGroupScheme (Spec (CommRingCat.of F))} (a : Z.toGrp ⟶ m.scheme)

set_option hygiene false in
local notation "M" => levi p
set_option hygiene false in
local notation "C" => m.splitCenter a

variable [(C).Normal] [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "L" => K.comap (M).subtype continuous_subtype_val

/-- The Haar measure assigning mass one to the quotient image of the
specified compact trace in the literal Levi. -/
def sourceQuotientHaar : Measure (M ⧸ C) :=
  RankinSelberg.normalizedCompactOpenHaar (quotientTrace C L)
    (quotientTrace_isCompact C L (isCompact_leviLevel p K.toSubgroup hK))

instance sourceQuotientHaar_isHaar : (m.sourceQuotientHaar a K hK).IsHaarMeasure :=
  RankinSelberg.normalizedCompactOpenHaar_isHaar _ _

/-- The literal trace has the source quotient mass. -/
theorem sourceQuotientHaar_normalized :
    IsNormalizedQuotientHaar C L (m.sourceQuotientHaar a K hK) :=
  RankinSelberg.normalizedCompactOpenHaar_self _ _

/-- For the actual split component of the closed Levi model the source Haar
is invariant under inversion. -/
theorem sourceQuotientHaar_isInvInvariant (ha : IsSplitComponent a) :
    (m.sourceQuotientHaar a K hK).IsInvInvariant := by
  let : IsAffine m.scheme.X.left :=
    let := m.reductive.isAffineHom
    isAffine_of_isAffineHom m.scheme.X.hom
  have hC : IsClosed (C : Set M) :=
    m.pointHomeomorph.toHomeomorph.isClosedMap _ (isClosed_range_splitComponent m.scheme a ha)
  let : IsClosed (C : Set M) := hC
  let : LocallyCompactSpace M := (isClosed_levi_of_model m).locallyCompactSpace
  let : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology _
  let mu := m.sourceQuotientHaar a K hK
  let : mu.Regular := RankinSelberg.normalizedCompactOpenHaar_regular _ _
  let : mu.IsMulRightInvariant :=
    Haar.centralSubgroupQuotient_isMulRightInvariant C (m.splitCenter_le_center a ha)
      hC (levi_modularCharacter m) mu
  exact Langlands.isInvInvariant_of_isMulRightInvariant mu

end Langlands.HarishChandraSchwartz.RationalSemistandard.LeviModel
