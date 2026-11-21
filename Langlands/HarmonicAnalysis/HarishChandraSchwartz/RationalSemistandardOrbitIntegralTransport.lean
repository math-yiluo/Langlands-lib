import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardComparisonOrbitMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardComparisonHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceFormalDegree

/-! # One-orbit source integral transport under normalized comparison -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WeylSectionComparisonData

open InvariantComparison

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean SourceMeasure.modelAffineHom SourceMeasure.modelAffine
  SourceMeasure.modelTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  {a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme}
  {ha : ∀ p, IsSplitComponent (a p)}
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  {mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p))}
  [∀ p, (mu p).IsHaarMeasure]
  {d : ∀ p : SemistandardSpectralIndex i, CompactData p}
  {hG : IsConnectedReductive G}
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
set_option quotPrecheck false in
local notation "SectionAt" => rationalSemistandardThetaComponentSpace a ha mu d
set_option hygiene false in local notation "O" => GlobalForm.OrbitPoint a ha mu
set_option hygiene false in local notation "M" p:max => chosenLeviModel p
set_option hygiene false in local notation "Center" p:max => (M p).splitCenter (a p)
set_option hygiene false in
local notation "central" p:max => (M p).splitCenter_le_center (a p) (ha p)

variable (t : Θ) (q : SemistandardSpectralIndex i) (n : C.Lift t q)

set_option hygiene false in
local notation "tq" => C.target t q n
set_option hygiene false in
local notation "eO" => orbitPointComparison t C q n
set_option hygiene false in
local notation "T" => C.smoothComparison t q n

/-- The coefficient function used by the actual component packet. -/
def componentCoefficient (x : Θ) :
    SectionAt x →ₗ[ℂ] (O x → LocallyConstant (rationalPoints G) ℂ) :=
  SourcePacket.coefficientMap hG (M x.1)
    (C.presentation x.1) (d x.1) (base a ha mu x) (Center x.1) (central x.1) (mu x.1)
    (squareIntegrableBase x)

set_option hygiene false in local notation "coef" => componentCoefficient C

/-- The remaining coefficient comparison at the literal actual inducing
representatives, with the actual normalized comparison on sections. -/
def CoefficientTransportStatement : Prop :=
  ∀ (t : Θ) (q : SemistandardSpectralIndex i) (n : C.Lift t q)
    (v : SectionAt t) (A : Representatives a ha mu t),
    coef (tq) (T v) (GlobalSynthesis.componentOrbitPoint a ha mu (tq) (C.representative t q n A)) =
      coef t v (GlobalSynthesis.componentOrbitPoint a ha mu t A)

/-- Fiberwise coefficient transport gives equality across the literal orbit
homeomorphism, including at independently chosen target base. -/
theorem coefficient_orbitPointComparison (h : CoefficientTransportStatement C)
    (v : SectionAt t) (x : O t) :
    coef (tq) (T v) (eO x) = coef t v x := by
  obtain ⟨A, hA⟩ := GlobalSynthesis.componentOrbitPoint_surjective a ha mu t x
  have hp := congrArg (fun y : O (tq) => coef (tq) (T v) y)
    ((congrArg (eO) hA.symm).trans (orbitPointComparison_representative t C q n A))
  have hs := congrArg (fun y : O t => coef t v y) hA
  exact hp.trans ((h t q n v A).trans hs)

variable (Q : ∀ x : Θ, OrbitPacketData (C.presentation x.1) (base a ha mu x))

set_option hygiene false in
local notation "density" => GlobalForm.componentDensity hG a ha mu C.presentation Q

/-- The exact density comparison for the actual continued scalars on both
parabolics, using the same source compact as the normalized tensor. -/
def DensityTransportStatement : Prop :=
  (∀ x : Θ, (Q x).compact = (d x.1).compact) →
  ∀ (t : Θ) (q : SemistandardSpectralIndex i) (n : C.Lift t q) (x : O t),
    density (C.target t q n) (orbitPointComparison t C q n x) = density t x

variable [∀ p, IsAffine (Z p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal]
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)

set_option hygiene false in
local notation "packet" => GlobalSynthesis.componentPacket hG a ha mu d C.presentation hindex Q

/-- The source wave packets agree under actual normalized comparison once
the literal coefficients and the actual densities have been compared. -/
theorem componentPacket_transport (hE : CoefficientTransportStatement C)
    (hD : DensityTransportStatement C Q) (hQ : ∀ x : Θ, (Q x).compact = (d x.1).compact)
    (v : SectionAt t) :
    packet (tq) (T v) = packet t v := by
  funext g
  change (∫ y : O (tq), density (tq) y * coef (tq) (T v) y g
    ∂GlobalSynthesis.componentOrbitMeasure a ha mu hindex (tq)) =
      ∫ x : O t, density t x * coef t v x g ∂GlobalSynthesis.componentOrbitMeasure a ha mu hindex t
  let f : O (tq) → ℂ := fun y => density (tq) y * coef (tq) (T v) y g
  have hf := (orbitPointComparison_measurePreserving t C q n hindex).integral_comp
    (eO).toMeasurableEquiv.measurableEmbedding f
  refine hf.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
  exact congrArg₂ (· * ·) (hD hQ t q n x)
    (congrArg (fun f : LocallyConstant (rationalPoints G) ℂ => f g)
      (coefficient_orbitPointComparison C t q n hE v x))

/-- The inverse smooth comparison transports the target packet back to
the source, as used in the VI.3 average. -/
theorem componentPacket_transport_symm (hE : CoefficientTransportStatement C)
    (hD : DensityTransportStatement C Q) (hQ : ∀ x : Θ, (Q x).compact = (d x.1).compact)
    (v : SectionAt (tq)) :
    packet t ((T).symm v) = packet (tq) v :=
  (componentPacket_transport C t q n Q hindex hE hD hQ ((T).symm v)).symm.trans
    (congrArg (packet (tq)) ((T).apply_symm_apply v))

section Form

variable [∀ p, (mu p).IsInvInvariant]

/-- The inverse-degree pairing used by the actual component integral. -/
def componentPairing (x : Θ) (v w : SectionAt x) (y : O x) : ℂ :=
  SourceForm.pairing hG (M x.1)
    (C.presentation x.1) (d x.1) (base a ha mu x) (Center x.1) (central x.1) (mu x.1)
    (squareIntegrableBase x) v w y

set_option hygiene false in local notation "pairing" => componentPairing C

set_option hygiene false in
local notation "degree" x:max => SourceDegree.orbitDegree (M x.1) (d x.1)
  (a x.1) (ha x.1) (mu x.1) x.2

/-- The remaining transport of the actual Schur degree and induced tensor
pairing under the absolute scale of the literal split-central quotients. -/
def PairingTransportStatement : Prop :=
  SourceMeasure.IntrinsicQuotientNormalization a mu d →
  ∀ (t : Θ) (q : SemistandardSpectralIndex i) (n : C.Lift t q),
    degree (tq) = degree t ∧
    ∀ (v w : SectionAt t) (A : Representatives a ha mu t),
      pairing (tq) (T v) (T w) (GlobalSynthesis.componentOrbitPoint a ha mu (tq) (C.representative t q n A)) =
      pairing t v w (GlobalSynthesis.componentOrbitPoint a ha mu t A)

omit [∀ p, IsAffine (Z p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal] in
/-- The literal coefficient pairings agree at corresponding orbit points. -/
theorem pairing_orbitPointComparison (h : PairingTransportStatement C)
    (hn : SourceMeasure.IntrinsicQuotientNormalization a mu d)
    (v w : SectionAt t) (x : O t) :
    pairing (tq) (T v) (T w) (eO x) = pairing t v w x := by
  obtain ⟨A, hA⟩ := GlobalSynthesis.componentOrbitPoint_surjective a ha mu t x
  have hp := congrArg (fun y : O (tq) => pairing (tq) (T v) (T w) y)
    ((congrArg (eO) hA.symm).trans (orbitPointComparison_representative t C q n A))
  have hs := congrArg (fun y : O t => pairing t v w y) hA
  exact hp.trans (((h hn t q n).2 v w A).trans hs)

set_option hygiene false in
local notation "form" => GlobalForm.componentForm hG a ha mu d C.presentation hindex Q

/-- The actual density-weighted inverse-degree form agrees on one orbit
once the preceding scalar and source pairing comparisons hold. -/
theorem componentForm_transport (hB : PairingTransportStatement C)
    (hn : SourceMeasure.IntrinsicQuotientNormalization a mu d)
    (hD : DensityTransportStatement C Q) (hQ : ∀ x : Θ, (Q x).compact = (d x.1).compact)
    (v w : SectionAt t) :
    form (tq) (T v) (T w) = form t v w := by
  change (∫ y : O (tq), density (tq) y * pairing (tq) (T v) (T w) y
    ∂GlobalSynthesis.componentOrbitMeasure a ha mu hindex (tq)) =
      ∫ x : O t, density t x * pairing t v w x ∂GlobalSynthesis.componentOrbitMeasure a ha mu hindex t
  let f : O (tq) → ℂ := fun y => density (tq) y * pairing (tq) (T v) (T w) y
  have hf := (orbitPointComparison_measurePreserving t C q n hindex).integral_comp
    (eO).toMeasurableEquiv.measurableEmbedding f
  refine hf.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
  exact congrArg₂ (· * ·) (hD hQ t q n x)
    (pairing_orbitPointComparison C t q n hB hn v w x)

end Form

end Langlands.HarishChandraSchwartz.RationalSemistandard.WeylSectionComparisonData
