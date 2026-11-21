import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacketFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylOrbitMeasure

/-! # Waldspurger VII.2.2(ii) for actual semistandard wave packets -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact (HasWeylRepresentatives)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing

open Association WeylOrbits WeylSections WeylComparison
open ActualConjugateLeviCoherence (LeviNormalization)
open WaldspurgerSourceNormalization (IsSourceCompactAt)

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G)
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (rs : ∀ p : SemistandardSpectralIndex i, CocharacterPresentation hG p)

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "Point" => GlobalForm.OrbitPoint a ha mu
set_option hygiene false in
local notation "Sections" => rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d
set_option hygiene false in
local notation "model" p:max => chosenLeviModel p
set_option hygiene false in
local notation "Center" p:max => (model p).splitCenter (a p)
set_option hygiene false in
local notation "Central" p:max => (model p).splitCenter_le_center (a p) (ha p)
set_option hygiene false in
local notation "base" t:max => orbitRepresentative (model t.1) (a t.1) (ha t.1) (mu t.1) t.2
set_option hygiene false in
local notation "sqBase" t:max =>
  orbitRepresentative_isSquareIntegrable (model t.1) (a t.1) (ha t.1) (mu t.1) t.2
set_option hygiene false in
local notation "Rep" t:max => UnitaryOrbitRepresentative (model t.1).normCharacters (base t)
set_option hygiene false in
local notation "pointAt" t:max => unitaryOrbitRepresentativeDiscreteSeriesOrbit (model t.1).normCharacters
  (base t) (Center t.1) (Central t.1) (mu t.1) (sqBase t)
set_option hygiene false in
local notation "omegaBase" t:max => discreteSeriesClass (Center t.1) (Central t.1) (mu t.1) (base t) (sqBase t)
set_option hygiene false in
local notation "hCentralizer" p:max => sourceTorusCentralizer_le_levi (rs p)
set_option hygiene false in
local notation "eta" t:max => SourceMeasure.normalizedOrbitMeasure (model t.1)
  (a t.1) (ha t.1) (hindex t.1) (mu t.1) (omegaBase t)

section PointTransport

variable (t t' : Theta) (hw : HasWeylRepresentatives i (d t.1).compact.toSubgroup)

set_option hygiene false in
local notation "OW" => OrbitWeylTransporters a ha mu t t' (hCentralizer t.1)
set_option hygiene false in
local notation "lift" => compactWeylLift (q := t'.1) (d t.1) (hCentralizer t.1) hw
set_option hygiene false in
local notation "hc" w:max =>
  compactLiftConjugatesLevi (d t.1) (hCentralizer t.1) (lift (Subtype.val w)).val
set_option hygiene false in
local notation "target" w:max => conjugateFullIndex a ha mu t t'.1 (hc w)
set_option hygiene false in
local notation "targetOrbit" w:max => compactLift_targetOrbit hG a ha mu d rs t t' w
  (lift (Subtype.val w)).val (lift (Subtype.val w)).property
set_option hygiene false in
local notation "targetRep" w:max => compactLiftTargetRepresentative hG a ha mu d rs t t'
  (lift (Subtype.val w)).val (targetOrbit w)

/-- Conjugate the inducing class and regard it as a point of the specified target orbit. -/
def orbitWeylPointMap (w : OW) (omega : Point t) : Point t' :=
  let omega' := conjugateOrbitPoint a ha mu t t'.1 (hc w) omega
  orbitPointOfClass a ha mu t' omega'.val
    ((orbitPoint_mk a ha mu (target w) omega').trans (targetOrbit w))

/-- The point map uses the same inducing representative as the normalized comparison. -/
theorem orbitWeylPointMap_representative (w : OW) (A : Rep t) :
    orbitWeylPointMap hG a ha mu d rs t t' hw w ((pointAt t) A) =
      (pointAt t') ((targetRep w) A) := by
  apply Subtype.ext
  apply Subtype.ext
  change (conjugateOrbitPoint a ha mu t t'.1 (hc w) ((pointAt t) A)).val.val =
    Quotient.mk _ ((targetRep w) A).val
  exact (congrArg (fun omega : Point (target w) => omega.val.val)
    (conjugateOrbitPoint_representative a ha mu t t'.1 (hc w) A)).trans
      (congrArg (Quotient.mk _)
        (compactLift_conjugateRepresentative_val hG a ha mu d rs t (lift w.val).val A).symm)

variable [∀ p, IsAffine (T p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal]
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)

/-- The compact lift preserves the source-normalized orbit measure at the chosen target base. -/
theorem orbitWeylPointMap_measurePreserving (w : OW) :
    MeasurePreserving (orbitWeylPointMap hG a ha mu d rs t t' hw w) (eta t) (eta t') := by
  let pushOrbit := conjugateOrbit (hc w) (model t.1) (model t'.1)
    (a t.1) (ha t.1) (a t'.1) (ha t'.1) (mu t.1) (mu t'.1)
  have hbase :=
    (congrArg pushOrbit
      (mk_discreteSeriesClass_orbitRepresentative (model t.1) (a t.1) (ha t.1) (mu t.1) t.2)).trans
      ((targetOrbit w).trans
        (mk_discreteSeriesClass_orbitRepresentative (model t'.1) (a t'.1) (ha t'.1)
          (mu t'.1) t'.2).symm)
  let e : Point t ≃ₜ Point t' := SourceMeasure.orbitConjugationRecentered
    (hc w) (model t.1) (model t'.1) (a t.1) (ha t.1) (a t'.1) (ha t'.1)
    (mu t.1) (mu t'.1) (omegaBase t) hbase
  have hmap : orbitWeylPointMap hG a ha mu d rs t t' hw w = (e : Point t → Point t') := by
    funext omega
    apply Subtype.ext
    exact (SourceMeasure.orbitConjugationRecentered_val
      (hc w) (model t.1) (model t'.1) (a t.1) (ha t.1) (a t'.1) (ha t'.1)
      (mu t.1) (mu t'.1) (omegaBase t) hbase omega).symm
  rw [hmap]
  exact ⟨e.continuous.measurable, SourceMeasure.normalizedOrbitMeasure_map_conjugationRecentered
    (hc w) (model t.1) (model t'.1) (a t.1) (ha t.1) (a t'.1) (ha t'.1)
    (mu t.1) (mu t'.1) (omegaBase t) hbase (hindex t.1) (hindex t'.1)⟩

end PointTransport

variable [∀ p, IsAffine (T p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal]
  [∀ p, (mu p).IsInvInvariant]
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)
  (Q : ∀ t : Theta, OrbitPacketData (rs t.1) (base t))

set_option hygiene false in
local notation "Density" => GlobalForm.componentDensity hG a ha mu rs Q
set_option hygiene false in
local notation "pair" t:max => SourceForm.pairing hG (model t.1) (rs t.1) (d t.1) (base t)
  (Center t.1) (Central t.1) (mu t.1) (sqBase t)
set_option hygiene false in
local notation "repForm" t:max => SourceForm.representativeForm hG (model t.1) (rs t.1) (d t.1)
  (base t) (Center t.1) (Central t.1) (mu t.1) (sqBase t)

section OrbitIntegrals

variable (t t' : Theta) (hw : HasWeylRepresentatives i (d t.1).compact.toSubgroup)

set_option hygiene false in
local notation "OW" => OrbitWeylTransporters a ha mu t t' (hCentralizer t.1)
set_option hygiene false in
local notation "pointMap" => orbitWeylPointMap hG a ha mu d rs t t' hw

/-- The exact scalar input in the VII.2.2(ii) change of variables. -/
def OrbitWeylDensityTransportStatement : Prop :=
  ∀ (w : OW) (omega : Point t), Density t omega = Density t' (pointMap w omega)

variable (hk : (d t'.1).compact = (d t.1).compact)
  (D : LeviNormalization (rs t.1).hom (dynamicInducing (rs t.1) (base t).obj))
  (hD : HasIntrinsicSourceNormalization (d t.1) (base t) (rs t.1) D)
  (hdesc : OrbitWeylDescentStatement hG a ha mu d rs t t' hk D)

set_option hygiene false in
local notation "compare" => normalizedWeylSection hG a ha mu d rs t t' hk D hw hD hdesc

/-- Source density times the inverse-formal-degree pairing at the conjugated point. -/
def orbitWeylPairingIntegrand (w : OW) (v : Sections t) (v' : Sections t') (omega : Point t) : ℂ :=
  Density t omega * (pair t') v' (compare w v) (pointMap w omega)

set_option hygiene false in
local notation "integrand" => orbitWeylPairingIntegrand hG a ha mu d rs Q t t' hw hk D hD hdesc
set_option hygiene false in
local notation "lift" => compactWeylLift (q := t'.1) (d t.1) (hCentralizer t.1) hw
set_option hygiene false in
local notation "targetRep" w:max => compactLiftTargetRepresentative hG a ha mu d rs t t'
  (lift (Subtype.val w)).val
  (compactLift_targetOrbit hG a ha mu d rs t t' w
    (lift (Subtype.val w)).val (lift (Subtype.val w)).property)

omit [∀ p, IsAffine (T p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal] in
/-- The integrand evaluates with the given source representation and its actual forward pullback. -/
theorem orbitWeylPairingIntegrand_representative (w : OW) (v : Sections t) (v' : Sections t')
    (A : Rep t) :
    integrand w v v' ((pointAt t) A) =
      Density t ((pointAt t) A) *
        ((repForm t') ((targetRep w) A)).inner
          (v'.val ((targetRep w) A)) ((compare w v).val ((targetRep w) A)) := by
  unfold orbitWeylPairingIntegrand
  rw [orbitWeylPointMap_representative]
  exact congrArg (fun z : ℂ => Density t ((pointAt t) A) * z)
    (SourceForm.pairing_representative hG (model t'.1) (rs t'.1) (d t'.1)
      (base t') (Center t'.1) (Central t'.1) (mu t'.1) (sqBase t') v' (compare w v) ((targetRep w) A))

/-- All scalar source-orbit integrals in the finite expression converge. -/
def OrbitWeylPairingIntegrabilityStatement : Prop :=
  ∀ (w : OW) (v : Sections t) (v' : Sections t'), Integrable (integrand w v v') (eta t)

/-- The measured change of variables gives both convergence and the target-orbit component form. -/
theorem orbitWeylPairing_changeVariables
    (hdensity : OrbitWeylDensityTransportStatement hG a ha mu d rs Q t t' hw)
    (w : OW) (v : Sections t) (v' : Sections t') :
    Integrable (integrand w v v') (eta t) ∧
      (∫ omega, integrand w v v' omega ∂eta t) =
        GlobalForm.componentForm hG a ha mu d rs hindex Q t' v' (compare w v) := by
  have hmeasure := orbitWeylPointMap_measurePreserving hG a ha mu d rs t t' hw hindex w
  let f := fun omega : Point t' => Density t' omega * (pair t') v' (compare w v) omega
  have hf : Integrable f (eta t') :=
    SourceForm.integrable_pairing hG (model t'.1) (rs t'.1) (d t'.1)
      (a t'.1) (ha t'.1) (hindex t'.1) (mu t'.1) (base t') (sqBase t') (Q t') v' (compare w v)
  have heq : integrand w v v' = f ∘ pointMap w := by
    funext omega
    exact congrArg (fun z => z * (pair t') v' (compare w v) (pointMap w omega)) (hdensity w omega)
  simp only [heq]
  refine ⟨hmeasure.integrable_comp_of_integrable hf, ?_⟩
  change (∫ omega, f (pointMap w omega) ∂eta t) = ∫ omega, f omega ∂eta t'
  have hfmap : AEStronglyMeasurable f ((eta t).map (pointMap w)) := by
    rw [hmeasure.map_eq]
    exact hf.aestronglyMeasurable
  rw [← integral_map hmeasure.measurable.aemeasurable hfmap, hmeasure.map_eq]

/-- The exact integrability proposition follows from actual orbit change of variables. -/
theorem orbitWeylPairingIntegrability_of_changeOfVariables
    (hdensity : OrbitWeylDensityTransportStatement hG a ha mu d rs Q t t' hw) :
    OrbitWeylPairingIntegrabilityStatement hG a ha mu d rs hindex Q t t' hw hk D hD hdesc :=
  fun w v v' => (orbitWeylPairing_changeVariables hG a ha mu d rs hindex Q t t' hw hk D hD hdesc
    hdensity w v v').1

variable {K : OpenSubgroup (rationalPoints G)} (hK : IsCompact (K : Set (rationalPoints G)))
  (hi : IsMaximalSplitTorus i)

/-- The actual finite Weyl sum of scalar integrals in Waldspurger VII.2.2(ii). -/
def orbitWeylPairingSum (v : Sections t) (v' : Sections t') : ℂ :=
  letI := hG.finite_relativeWeylGroup i hi
  (sourceWeylScale hG rs hK t.1 : ℂ) * orbitWeylSum a ha mu t t' (hCentralizer t.1)
    (fun w => ∫ omega, integrand w v v' omega ∂eta t)

/-- An empty orbit transporter gives zero in the conjugate-Levi formula. -/
theorem orbitWeylPairingSum_of_isEmpty [IsEmpty OW] (v : Sections t) (v' : Sections t') :
    orbitWeylPairingSum hG a ha mu d rs hindex Q t t' hw hk D hD hdesc hK hi v v' = 0 := by
  let _ := hG.finite_relativeWeylGroup i hi
  simp only [orbitWeylPairingSum, orbitWeylSum_of_isEmpty, mul_zero]

end OrbitIntegrals

section ConjugatePairing

variable {nu : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

set_option hygiene false in
local notation "Packet" => GlobalSynthesis.componentPacket hG a ha mu d rs hindex Q
set_option hygiene false in
local notation "dg" => RationalDynamicSource.ambientHaar K hK

/-- Waldspurger VII.2.2(ii) for literal conjugate Levis, including an empty orbit sum. -/
def ConjugatePairingStatement : Prop :=
  ∀ (hi : IsMaximalSplitTorus i) (_ : IsGenericCocharacter i nu)
    (_ : SquareIntegrableWeight dg (rationalXi hK hPK) (rationalHeight (F := F) rho))
    (hsource : SourceCompactCompatibility hG a ha mu d rs Q (nu := nu) (K := K))
    (hcompact : IsSourceCompactAt i K.toSubgroup)
    (hhaar : ∀ p, SourceLeviQuotientHaar a mu (K := K) p)
    (_ : ComponentSchwartzMembershipStatement hG a ha mu d rs hindex Q hK hPK rho)
    (t t' : Theta), LevisConjugate t.1 t'.1 →
    ∀ (v : Sections t) (v' : Sections t')
      (D : LeviNormalization (rs t.1).hom (dynamicInducing (rs t.1) (base t).obj))
      (hmatch : LeviNormalizationMatches hG a ha mu rs t D),
      let hw := hasWeylRepresentatives_of_sourceCompact hG a ha mu d rs Q hsource t.1
      let hk := (hsource.2.1 t'.1).trans (hsource.2.1 t.1).symm
      let hD := hasIntrinsicSourceNormalization_of_commonCompact hG a ha mu d rs t D
        (hsource.2.1 t.1) hcompact (hhaar t.1) hmatch
      ∀ (hdesc : OrbitWeylDescentStatement hG a ha mu d rs t t' hk D),
        OrbitWeylDensityTransportStatement hG a ha mu d rs Q t t' hw →
        HarishChandraSchwartz.pairing dg (Packet t' v') (Packet t v) =
          orbitWeylPairingSum hG a ha mu d rs hindex Q t t' hw hk D hD hdesc hK hi v v'

end ConjugatePairing

end Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing
