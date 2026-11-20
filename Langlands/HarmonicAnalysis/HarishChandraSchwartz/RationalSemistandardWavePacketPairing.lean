import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeightedSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Pairing actual semistandard wave packets and VII.2.2(i) -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

/-- Conjugacy of the literal Levi subgroups by a point of the actual ambient group. -/
def LevisConjugate (p p' : SemistandardSpectralIndex i) : Prop :=
  ∃ g : rationalPoints G, (levi p).map (MulAut.conj g).toMonoidHom = levi p'

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- All-test rational conjugacy induces the literal conjugacy used in VII.2.2. -/
theorem levisConjugate_of_isRationallyConjugate {p p' : SemistandardSpectralIndex i}
    (h : p.levi.IsRationallyConjugate p'.levi) : LevisConjugate p p' := by
  obtain ⟨g, hg⟩ := h.symm
  refine ⟨g⁻¹, ?_⟩
  have hpts := congrArg (fun H : SubgroupFunctor G => H.rationalPoints) hg
  rw [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] at hpts
  exact hpts.symm

variable (hG : IsConnectedReductive G)
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ p, IsAffine (T p).X.left]
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, (rationalPoints.map (a p)).range.Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (rs : ∀ p : SemistandardSpectralIndex i, CocharacterPresentation hG p)
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (rs theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  {nu : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "sections" => rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d
set_option hygiene false in
local notation "packet" => GlobalSynthesis.componentPacket hG a ha mu d rs hindex Q
set_option hygiene false in
local notation "sourceHaar" => RationalDynamicSource.ambientHaar K hK

/-- The source uses one special compact for the coefficient and scalar pictures. -/
def SourceCompactCompatibility : Prop :=
  BruhatTits.SpecialCompact.SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)) ∧
  (∀ p, (d p).compact = K) ∧ (∀ theta : Theta, (Q theta).compact = K)

/-- VI.3.1 membership of each actual one-orbit packet. -/
def ComponentSchwartzMembershipStatement : Prop :=
  ∀ (theta : Theta) (v : sections theta),
    packet theta v ∈ schwartzSubmodule (rationalXi hK hPK) (rationalHeight (F := F) rho)

/-- Every smooth section is an input of the published component continuity target. -/
theorem componentSchwartzMembership_of_componentContinuity
    (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
    (hsource : SourceCompactCompatibility hG a ha mu d rs Q (nu := nu) (K := K))
    (hcont : GlobalSynthesis.ComponentContinuityStatement hG a ha mu d rs hindex Q
      K hK hPK rho) :
    ComponentSchwartzMembershipStatement hG a ha mu d rs hindex Q hK hPK rho := by
  intro theta v
  obtain ⟨synth, hsynth⟩ := hcont hi hnu hsource.1 hsource.2.1 hsource.2.2 theta
  have hv : (↑(synth v) : rationalPoints G → ℂ) = packet theta v := funext (hsynth v)
  rw [← hv]
  exact (synth v).property

/-- Codomain restriction of the actual packet along the preceding Schwartz membership. -/
def schwartzPacket
    (hmem : ComponentSchwartzMembershipStatement hG a ha mu d rs hindex Q hK hPK rho)
    (theta : Theta) : sections theta →ₗ[ℂ] RationalSchwartzSpace hK hPK rho :=
  (packet theta).codRestrict _ (hmem theta)

@[simp] theorem schwartzPacket_apply
    (hmem : ComponentSchwartzMembershipStatement hG a ha mu d rs hindex Q hK hPK rho)
    (theta : Theta) (v : sections theta) (g : rationalPoints G) :
    schwartzPacket hG a ha mu d rs hindex Q hK hPK rho hmem theta v g = packet theta v g := rfl

/-- The ambient scalar integrand of VII.2.2 is integrable for two Schwartz packets. -/
theorem integrable_pairing
    (hsw : SquareIntegrableWeight sourceHaar (rationalXi hK hPK) (rationalHeight (F := F) rho))
    (hmem : ComponentSchwartzMembershipStatement hG a ha mu d rs hindex Q hK hPK rho)
    (theta theta' : Theta) (v : sections theta) (v' : sections theta') :
    Integrable (fun g => conj (packet theta' v' g) * packet theta v g) sourceHaar := by
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hK⟩⟩
  exact Space.integrable_conj_mul (rationalL2Weights K.isOpen hK hPK rho hsw)
    (schwartzPacket hG a ha mu d rs hindex Q hK hPK rho hmem theta' v')
    (schwartzPacket hG a ha mu d rs hindex Q hK hPK rho hmem theta v)

/-- Waldspurger VII.2.2(i), with actual source Haar and literal rational Levi conjugacy. -/
def NonconjugatePairingStatement : Prop :=
  IsMaximalSplitTorus i → IsGenericCocharacter i nu →
  SourceCompactCompatibility hG a ha mu d rs Q (nu := nu) (K := K) →
  ComponentSchwartzMembershipStatement hG a ha mu d rs hindex Q hK hPK rho →
  ∀ (theta theta' : Theta), ¬ LevisConjugate theta.1 theta'.1 →
    ∀ (v : sections theta) (v' : sections theta'),
      HarishChandraSchwartz.pairing sourceHaar (packet theta' v') (packet theta v) = 0

end Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing
