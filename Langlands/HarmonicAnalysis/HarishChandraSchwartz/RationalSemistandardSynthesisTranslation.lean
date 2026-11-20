import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSpectralAction

/-! # Translation of the actual semistandard synthesis -/

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance synthesisTranslationParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (mu t).IsHaarMeasure]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "model(" t ")" => chosenLeviModel (t : Theta).1
set_option hygiene false in
local notation "center(" t ")" => (model(t)).splitCenter (a (t : Theta).1)
set_option hygiene false in
local notation "central(" t ")" => (model(t)).splitCenter_le_center (a (t : Theta).1) (ha (t : Theta).1)
set_option hygiene false in
local notation "rep(" t ")" =>
  orbitRepresentative (model(t)) (a (t : Theta).1) (ha (t : Theta).1) (mu (t : Theta).1) (t : Theta).2
set_option hygiene false in
local notation "sq(" t ")" =>
  orbitRepresentative_isSquareIntegrable (model(t)) (a (t : Theta).1) (ha (t : Theta).1)
    (mu (t : Theta).1) (t : Theta).2

variable (hG : IsConnectedReductive G)
  (rs : ∀ p : SemistandardSpectralIndex i, CocharacterPresentation hG p)
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)
  (Q : ∀ t : Theta, OrbitPacketData (rs t.1) (rep(t)))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))

set_option hygiene false in
local notation "component" => rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d
set_option hygiene false in
local notation "sectionAt" => rationalSemistandardThetaComponent a ha mu d
set_option hygiene false in
local notation "measureAt(" t ")" =>
  SourceMeasure.normalizedOrbitMeasure (model(t)) (a (t : Theta).1) (ha (t : Theta).1)
    (hindex (t : Theta).1) (mu (t : Theta).1)
    (discreteSeriesClass (center(t)) (central(t)) (mu (t : Theta).1) (rep(t)) (sq(t)))
set_option hygiene false in
local notation "coefficient(" t ")" =>
  SourcePacket.coefficientMap hG (model(t)) (rs (t : Theta).1) (d (t : Theta).1)
    (rep(t)) (center(t)) (central(t)) (mu (t : Theta).1) (sq(t))
set_option hygiene false in
local notation "density" => GlobalForm.componentDensity hG a ha mu rs Q
set_option hygiene false in
local notation "packet" => componentPacket hG a ha mu d rs hindex Q
set_option hygiene false in
local notation "smoothRep" => rationalSemistandardThetaSmoothRepresentation.{u, uV} a ha mu d

private theorem componentPacket_translate (t : Theta)
    (x : rationalPoints G × rationalPoints G) (v : component t) (g : rationalPoints G) :
    packet t (SourceForm.smoothAction (model(t)) (d t.1) (rep(t)) x v) g =
      packet t v (x.2⁻¹ * g * x.1) := by
  change (∫ omega, density t omega * coefficient(t)
      (SourceForm.smoothAction (model(t)) (d t.1) (rep(t)) x v) omega g ∂measureAt(t)) =
    ∫ omega, density t omega * coefficient(t) v omega (x.2⁻¹ * g * x.1) ∂measureAt(t)
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  exact congrArg (density t omega * ·)
    (unitaryOrbitCoefficientMap_action (decomposition t.1) (isClosed_radical t.1)
      (isClosed_parabolic t.1) (d t.1).compact (d t.1).isCompact (d t.1).factorization
      (ambient_modularCharacter hG) (parabolic_modularCharacter hG (model(t)) (rs t.1) (d t.1))
      (model(t)).normCharacters (rep(t)) (model(t)).continuous_normCharacters
      (d t.1).projection_continuous (center(t)) (central(t)) (mu t.1) (sq(t))
      (model(t)).unitaryCoordinates.toMulEquiv (model(t)).unitaryCoordinates_hasLaurent
      x v omega g)

/-- The actual weighted synthesis intertwines the product action on smooth
finite-support families with right and inverse-left translation. -/
def WeightedSynthesisTranslationStatement : Prop :=
  ∀ (x : rationalPoints G × rationalPoints G)
    (v : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d),
    weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 (smoothRep x v) =
      translate x.1 x.2 (weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 v)

theorem weightedSynthesis_translate :
    WeightedSynthesisTranslationStatement a ha mu d hG rs hindex Q K0 hK0 := by
  intro x v
  funext g
  change weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 (smoothRep x v) g =
    weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 v (x.2⁻¹ * g * x.1)
  rw [weightedSynthesis_apply, weightedSynthesis_apply]
  refine Finset.sum_congr ?_ fun t _ => ?_
  · ext t
    simp only [Set.Finite.mem_toFinset]
    exact Set.ext_iff.mp (rationalSemistandardThetaRepresentation_support a ha mu x v.val) t
  · exact congrArg ((sourceWeight hG rs K0 hK0 t.1 : ℂ) * ·)
      (componentPacket_translate a ha mu d hG rs hindex Q t x (sectionAt t v) g)

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis
