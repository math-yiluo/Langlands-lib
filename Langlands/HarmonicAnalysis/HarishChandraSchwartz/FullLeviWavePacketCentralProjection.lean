import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviWavePacketIsolation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviCoefficientPreimage
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralFiberAdapter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCentralMass
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSchwartzCentralConvergenceProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalLevelAveraging

/-! # Prescribing the actual central projection of a group-Levi wave packet -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)
set_option hygiene false in
local notation "νG" => (fun ψ => (rationalNormCharacters G ψ).toMul)
set_option hygiene false in
local notation "sL" => rationalFullLeviSplitComponent hG hi hν s
set_option hygiene false in
local notation "hsL" => isSplitComponent_rationalFullLeviSplitComponent hG hi hν s hs
set_option hygiene false in
local notation "A" => (rationalPoints.map s).range
set_option hygiene false in
local notation "hA" => hs.isCentralSplitTorus.isCentral.range_le_center
set_option hygiene false in
local notation "B" => rationalLeviSplitCenter Finset.univ sL
set_option hygiene false in
local notation "hB" => rationalLeviSplitCenter_le_center Finset.univ sL hsL
set_option hygiene false in
local notation "eG" => rationalFullLeviLiteralPointEquiv hG hi hν

variable [(A).Normal] [(B).Normal] [(rationalPoints.map sL).range.Normal]
  [MeasurableSpace (rationalPoints G ⧸ A)] [BorelSpace (rationalPoints G ⧸ A)]
  [MeasurableSpace (𝐌 ⧸ B)] [BorelSpace (𝐌 ⧸ B)]
  (mu : Measure (rationalPoints G ⧸ A)) [mu.IsHaarMeasure]

set_option hygiene false in
local notation "muM" => rationalFullLeviQuotientHaar hG hi hν s mu

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := rationalPoints G))
  (hsq : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation mu)

set_option hygiene false in
local notation "πM" => IrreducibleAdmissibleRep.pullback eG π
set_option hygiene false in
local notation "ω" => discreteSeriesClass A hA mu π hsq


variable {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "sections" =>
  rationalInducedSmoothOrbitSections hG hi hν Finset.univ hKc hPK πM
set_option hygiene false in
local notation "OG" => discreteSeriesOrbit A hA mu νG ω
set_option hygiene false in
local notation "x₀" => discreteSeriesOrbitMap A hA mu νG ω 1
set_option hygiene false in
local notation "tensor" => rationalFullLeviOrbitCoefficientTensor hG hi hν s hs mu π hsq hKc hPK
set_option hygiene false in
local notation "hindexG" => finiteIndex_splitValuationImage_of_isSplitComponent hG s hs
set_option hygiene false in
local notation "hcA" => hs.isCentralSplitTorus.isCentral

/-- The ambient normalized integral of the tensors attached to an actual
full-root section. -/
def rationalFullLeviAmbientWavePacket (q : sections) : rationalPoints G → ℂ :=
  rationalOrbitWavePacket s hcA mu hindexG ω (tensor q)

set_option hygiene false in
local notation "packet" => rationalFullLeviAmbientWavePacket hG hi hν s hs mu π hsq hKc hPK

variable (muA : Measure A) [muA.IsHaarMeasure]
  (χ : A →* ℂˣ) (hχ : Continuous χ) (hu : IsUnitaryCharacter χ)

include hχ hu in
set_option maxHeartbeats 500000 in
/-- Prescribe a coefficient at the base central character. Whenever the
selected section has integrable central translates, its ambient packet
projects to the prescribed coefficient times the actual split-central mass. -/
theorem exists_rationalFullLeviAmbientWavePacket_centralProjection
    (hπχ : classActsByCharacter A χ (ω).val) (t : CoefficientTensor π.obj) :
    ∃ q : sections,
      (∀ g : rationalPoints G,
        Integrable (fun a : A => packet q ((a : rationalPoints G) * g)) muA) →
      centralProjection muA χ (packet q) =
        (rationalSplitCentralMass s muA : ℂ) • (coefficientTensorMap π.obj t : rationalPoints G → ℂ) := by
  let eta := unitaryCircleCharacter χ hu.norm_eq_one
  let fiber := rationalOrbitCentralFiber s hcA mu ω eta
  let X : Set OG := fiber \ {x₀}
  have hX : X.Finite :=
    (finite_setOf_rationalOrbitCentralCharacter_eq s hcA mu hindexG ω eta).subset Set.sdiff_subset
  have hx₀ : x₀ ∉ X := fun h => h.2 (Set.mem_singleton _)
  have hbase : (x₀).val = ω := one_smul _ _
  have hω : x₀ ∈ fiber :=
    (mem_rationalOrbitCentralFiber_unitaryCircleCharacter_iff s hcA mu ω χ hu.norm_eq_one x₀).mpr
      (hbase.symm ▸ hπχ)
  obtain ⟨Φ, hΦ⟩ := exists_rationalFullLeviProductCoefficient_of_ambient hG hi hν π hKc hPK t
  obtain ⟨q, hq, hzero⟩ := exists_rationalFullLeviOrbitCoefficientTensor_finiteIsolation
    hG hi hν s hs mu π hsq hKc hPK Φ X hX hx₀
  have hv (x : OG) (hx : x ∈ fiber) (hne : x ≠ x₀) : tensor q x = 0 := hzero x ⟨hx, hne⟩
  have hcoef := hq.trans hΦ
  refine ⟨q, fun hint => ?_⟩
  funext g
  rw [centralProjection_eq_integral_unitaryCircleCharacter muA χ hu]
  have hcont := continuous_rationalFullLeviOrbitCoefficientTensor hG hi hν s hs mu π hsq hKc hPK q g
  have hinv := integral_central_rationalOrbitWavePacket_of_vanishing s hcA mu hindexG hG
    ω muA eta (continuous_unitaryCircleCharacter hu.norm_eq_one hχ) (tensor q) x₀ hω hv g hcont
    (hint g)
  exact hinv.trans (congrArg (fun c : LocallyConstant (rationalPoints G) ℂ =>
    (rationalSplitCentralMass s muA : ℂ) * c g) hcoef)

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)

set_option hygiene false in
local notation "cusp" => rationalCuspidalSubmodule hKc hPK ρ

variable (hpacket : ∀ q : sections, ∃ φ : RationalSchwartzSpace hKc hPK ρ,
  φ ∈ cusp ∧ (φ : rationalPoints G → ℂ) = packet q)

include hχ hu hρ hpacket in
set_option maxHeartbeats 500000 in
/-- A cuspidal Schwartz realization of the actual full-root packets gives
raw central-integral preimages of all the indicated tensor coefficients. -/
theorem mem_rationalCuspidalCentralImage_of_fullLeviPackets
    (hπχ : classActsByCharacter A χ (ω).val) (t : CoefficientTensor π.obj) :
    (coefficientTensorMap π.obj t : rationalPoints G → ℂ) ∈
      rationalCuspidalCentralImage hKc hPK ρ muA χ := by
  obtain ⟨q, hq⟩ := exists_rationalFullLeviAmbientWavePacket_centralProjection
    hG hi hν s hs mu π hsq hKc hPK muA χ hχ hu hπχ t
  obtain ⟨φ, hφ, hφq⟩ := hpacket q
  have hu₁ : IsUnitaryCharacter (1 : A →* ℂˣ) :=
    ⟨fun _ => by simp, by simpa only [MonoidHom.one_apply, Units.val_one] using measurable_const⟩
  have hc := rationalSchwartzCentralConvergence F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs
    muA (1 : A →* ℂˣ) continuous_const hu₁
  have hint (g : rationalPoints G) :
      Integrable (fun a : A => packet q ((a : rationalPoints G) * g)) muA := by
    have h := hc φ Submodule.mem_top g
    simpa only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul, hφq] using h
  have hp := (congrArg (centralProjection muA χ) hφq).trans (hq hint)
  exact mem_rationalCuspidalCentralImage_of_mass_smul s hKc hPK ρ hG hs muA χ hφ hp

include hχ hu hρ hpacket in
/-- The same packet realization yields an actual preimage at a compact open
level whenever the prescribed coefficient is bi-invariant at that level. -/
theorem mem_rationalCuspidalCentralLevelImage_of_fullLeviPackets
    (hπχ : classActsByCharacter A χ (ω).val) (t : CoefficientTensor π.obj)
    (H : OpenSubgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G)))
    (hbi : IsBiInvariant H.toSubgroup (coefficientTensorMap π.obj t : rationalPoints G → ℂ)) :
    (coefficientTensorMap π.obj t : rationalPoints G → ℂ) ∈
      rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H.toSubgroup := by
  have hc := rationalSchwartzCentralConvergence F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs
    muA χ hχ hu
  have hf := mem_rationalCuspidalCentralImage_of_fullLeviPackets
    hG hi hν s hs mu π hsq hKc hPK muA χ hχ hu ρ hρ hpacket hπχ t
  exact mem_rationalCuspidalCentralLevelImage_of_biInvariant hKc hPK ρ hs muA χ
    (hc.mono le_top) H hH hf hbi

end Langlands.HarishChandraSchwartz
