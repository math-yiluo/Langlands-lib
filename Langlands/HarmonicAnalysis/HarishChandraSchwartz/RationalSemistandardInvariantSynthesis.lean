import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAverage
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeightedSynthesis

/-! # Waldspurger's synthesis on invariant spectral families -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

variable (hG : IsConnectedReductive G)
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (mu t).IsHaarMeasure]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (rs theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
  (hi : IsMaximalSplitTorus i)
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})
  (hfin : SemistandardSpectralFiberFinitenessStatement.{u})

/-- The raw VI.3.2 equality uses the actual weighted integral and the
actual source average, as functions on the full smooth family. -/
def FactorizationStatement : Prop :=
  ∀ f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d,
    weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 f =
      weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 (Average.smoothAverage C hi hD hfin f)

variable {nu : cocharacterLattice S}
  {Kbase : OpenSubgroup (rationalPoints G)} (hKbase : IsCompact (Kbase : Set (rationalPoints G)))
  (hPKbase : IsIwasawaPair (standardParabolicPoints i nu ∅) (Kbase : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  (h : SchwartzMembershipStatement hG a ha mu d rs hindex Q K0 hK0 hKbase hPKbase rho)
  (hnu : IsGenericCocharacter i nu)
  (hspecial : SpecialCompactProperties F i nu (K0 : Subgroup (rationalPoints G)))
  (hd : ∀ t, (d t).compact = K0) (hQ : ∀ theta, (Q theta).compact = K0)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Synthesis" => schwartzSynthesis hG a ha mu d rs hindex Q K0 hK0 hKbase hPKbase rho
  h hfin hi hnu hspecial hd hQ

/-- Waldspurger's `κ` restricts the actual Schwartz-valued lift `κ̃` to the
conditional invariant space. -/
def invariantSynthesis :
    rationalSemistandardThetaInvariantSections C →ₗ[ℂ]
      RationalSchwartzSpace hKbase hPKbase rho :=
  (Synthesis).comp (rationalSemistandardThetaInvariantSections C).subtype

@[simp] theorem invariantSynthesis_apply
    (f : rationalSemistandardThetaInvariantSections C) (g : rationalPoints G) :
    invariantSynthesis hG a ha mu d rs hindex Q K0 hK0 C hi hfin hKbase hPKbase rho
        h hnu hspecial hd hQ f g =
      weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 f.val g := rfl

/-- VI.3.2 on the actual Schwartz-valued linear maps follows from its raw
function equality. The projector uses the exact image target for the average. -/
theorem schwartzSynthesis_factorization
    (haImage : Average.InvariantImageStatement C hi hD hfin)
    (hf : FactorizationStatement hG a ha mu d rs hindex Q K0 hK0 C hi hD hfin) :
    Synthesis =
      (invariantSynthesis hG a ha mu d rs hindex Q K0 hK0 C hi hfin hKbase hPKbase rho
        h hnu hspecial hd hQ).comp (Average.invariantProjector C hi hD hfin haImage) :=
  LinearMap.ext fun f => Subtype.ext (hf f)

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis
