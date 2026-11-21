import Langlands.BruhatTits.Unipotent.JacquetCompactContainmentProof
import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardCuspidalFourierVanishing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperPacketPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperSynthesisConvolution
import Langlands.Representation.Intertwining.PQIntegralIdentificationGroup

/-! # Proper semistandard packet vanishing in VIII.2.3 -/

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
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

local instance packetVanishingCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance packetVanishingParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {nu : cocharacterLattice S} (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

set_option hygiene false in
local notation "C" => RationalSchwartzSpace hKc hPK rho

private theorem radicalHaar_isInvInvariant (p : SemistandardSpectralIndex i)
    (r : CocharacterPresentation hG p) (muU : Measure (radical p)) [muU.IsHaarMeasure] :
    muU.IsInvInvariant := by
  let : LocallyCompactSpace (radical p) := (isClosed_radical p).locallyCompactSpace
  let : SecondCountableTopology (radical p) := TopologicalSpace.Subtype.secondCountableTopology _
  let : TopologicalSpace.MetrizableSpace (radical p) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  let : muU.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure muU
  have hlimit : Jacquet.Localization.IsLimitOfCompactSubgroups (radical p) := by
    change Jacquet.Localization.IsLimitOfCompactSubgroups p.radical.rationalPointSubgroup
    rw [← r.radical_eq]
    exact BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
      BruhatTits.dynamicUnipotentCompactOpenContainment F G hG r.hom
  let : muU.IsMulRightInvariant :=
    IntegralIdentification.isMulRightInvariant_of_forall_mem_compactOpen
      (IntegralIdentification.exists_compactOpen_of_isLimit _ (isClosed_radical p) hlimit) muU
  exact Langlands.isInvInvariant_of_isMulRightInvariant muU

private theorem properPacketTests_mem_cuspidal
    (rs : ∀ p : SemistandardSpectralIndex i, CocharacterPresentation hG p)
    (hcmp : RationalCuspidalSemistandardComparisonStatement.{u}) (hrho : IsClosedSubgroup rho)
    (f : C) (hf : f ∈ rationalCuspidalSubmodule hKc hPK rho) (g : rationalPoints G) :
    properPacketRightTest hG hi hnu hKc hPK rho f g ∈ rationalCuspidalSubmodule hKc hPK rho ∧
    properPacketLeftTest hG hi hnu hKc hPK rho f g ∈ rationalCuspidalSubmodule hKc hPK rho := by
  have hFull := (hcmp F G hG S i hi nu hnu K hKc hPK N rho hrho f).mp hf
  have hRaw (p : SemistandardSpectralIndex i) (hp : p.IsProper)
      (muU : Measure (radical p)) (hhaar : muU.IsHaarMeasure) :
      IsUnipotentCuspidal muU (f : rationalPoints G → ℂ) := by
    intro x y
    have h := congrFun (hFull p hp muU hhaar (y, x⁻¹)) (1 : levi p)
    simpa only [constantTermInd, constantTerm, translate_apply, Prod.fst, Prod.snd, map_one,
      Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one, one_mul, inv_inv,
      OneMemClass.coe_one, Pi.zero_apply] using h
  have hKernel (φ : C) (hφ : ∀ p : SemistandardSpectralIndex i, p.IsProper →
      ∀ (muU : Measure (radical p)), muU.IsHaarMeasure →
        IsUnipotentCuspidal muU (φ : rationalPoints G → ℂ)) :
      φ ∈ rationalCuspidalSubmodule hKc hPK rho := by
    apply (hcmp F G hG S i hi nu hnu K hKc hPK N rho hrho φ).mpr
    intro p hp muU hhaar xy
    funext m
    simp only [constantTermInd, constantTerm, translate_apply, Pi.zero_apply]
    have hIntegral :
        (∫ u : radical p, φ (xy.2⁻¹ * ((m : rationalPoints G) * (u : rationalPoints G)) *
          xy.1) ∂muU) = 0 := by
      simpa only [mul_assoc] using hφ p hp muU hhaar (xy.2⁻¹ * (m : rationalPoints G)) xy.1
    rw [hIntegral, mul_zero]
  constructor
  · apply hKernel
    intro p hp muU hhaar
    let := hhaar
    let := radicalHaar_isInvInvariant hG p (rs p) muU
    intro x y
    simpa only [properPacketRightTest_apply] using
      isUnipotentCuspidal_conj_mul_inv g (hRaw p hp muU hhaar) x y
  · apply hKernel
    intro p hp muU hhaar
    let := hhaar
    let := radicalHaar_isInvInvariant hG p (rs p) muU
    intro x y
    simpa only [properPacketLeftTest_apply] using
      isUnipotentCuspidal_conj_inv_mul g (hRaw p hp muU hhaar) x y

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (muM : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (muM t).IsHaarMeasure] [∀ t, (muM t).IsInvInvariant]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ t : RationalSemistandardTheta.{u, uV} a ha muM,
    OrbitPacketData (rs t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2))

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha muM
set_option hygiene false in
local notation "component" => rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d
variable {muG : Measure (rationalPoints G)} [muG.IsHaarMeasure] [muG.IsMulRightInvariant]
  [muG.IsInvInvariant] [SFinite muG]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (muM p) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

set_option hygiene false in
local notation "fourier" =>
  rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT

set_option hygiene false in
local notation "smoothFourier" =>
  rationalSemistandardFourierSmoothFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT

set_option hygiene false in
local notation "pairingIntegrability" =>
  ProperPacketConvolutionIntegrabilityStatement hG hi hnu hKc hPK rho a ha muM d rs hindex Q muG

/-- The VII.1.2 route to both proper-packet zeros of VIII.2.3. -/
def ProperPacketConvolutionFromFourierStatement : Prop :=
  RationalCuspidalSemistandardComparisonStatement.{u} → IsClosedSubgroup rho →
    (∀ (t : Theta), t.1.IsProper →
      ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
        muU.IsHaarMeasure ∧
          RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
            t.1 (chosenLeviModel t.1) (d t.1)
            (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
            muL muU XiM sigmaM) →
    (∀ (f : C) (t : Theta), fourier f t ∈ component t) → pairingIntegrability →
    ProperPacketConvolutionVanishingStatement hG a ha muM d rs hindex Q hKc hPK rho muG

set_option maxHeartbeats 2000000 in
theorem properPacketConvolutionFromFourier :
    ProperPacketConvolutionFromFourierStatement hG hi hnu hKc hPK rho a ha muM d rs hindex Q
      hsw hdelta hT := by
  intro hcmp hrho hin hsm hint f hf t ht v
  have hzero (φ : C) (hφ : φ ∈ rationalCuspidalSubmodule hKc hPK rho) :
      smoothFourier hsm φ t = 0 := by
    apply Subtype.ext
    exact rationalSemistandardCuspidalProperFourierVanishing hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT hcmp hrho hin φ hφ t ht
  have hpoint (g : rationalPoints G) :=
    properPacketConvolutionPairing hG hi hnu hKc hPK rho a ha muM d rs hindex Q
      hsw hdelta hT hsm hint f hf t ht v g
  have htests (g : rationalPoints G) :=
    properPacketTests_mem_cuspidal hG hi hnu hKc hPK rho rs hcmp hrho f hf g
  constructor
  · funext g
    rw [(hpoint g).1, hzero _ (htests g).1, map_zero]
    rfl
  · funext g
    rw [(hpoint g).2, hzero _ (htests g).2, map_zero]
    rfl

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis
