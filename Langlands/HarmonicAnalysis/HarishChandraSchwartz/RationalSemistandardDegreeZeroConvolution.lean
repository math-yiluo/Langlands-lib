import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardDegreeZero
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperSynthesisConvolution
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperPacketVanishing

/-! # Lemma VIII.2.3: convolution with the degree-zero operator -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

open RationalSemistandard

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance degreeZeroConvolutionCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance degreeZeroConvolutionParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) :=
  (isClosed_parabolic p).locallyCompactSpace

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (muM : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (muM t).IsHaarMeasure] [∀ t, (muM t).IsInvInvariant]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (hG : IsConnectedReductive G)
  (C : WeylSectionComparisonData.{u, uV} a ha muM d hG)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha muM

set_option hygiene false in
local notation "properPart" => rationalSemistandardThetaProperPart.{u, uV} a ha muM


variable {nu : cocharacterLattice S}
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsHaarMeasure] [muG.IsMulRightInvariant] [SFinite muG]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (muM p) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

set_option hygiene false in
local notation "Schwartz" => RationalSchwartzSpace hKc hPK rho

set_option hygiene false in
local notation "fourier" =>
  rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT

set_option hygiene false in
local notation "properFourier" =>
  rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT

variable (hgeo : Finite (SemistandardSpectralIndex i))
  (hcomp : RationalProperSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K)
  (hlow : RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (relativeRootRank i))
  (hS : RationalSemistandardFourierFamilySmoothnessStatement hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT)
  (hin : ∀ t : Θ,
    ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
      RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
        t.1 (chosenLeviModel t.1) (d t.1)
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
        muL muU XiM sigmaM)
  (hsplit : SemistandardProperSplitComparisonStatement.{u})
  (hcov : ∀ f : Schwartz, IsWeylInvariant C (fourier f))
  [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal]
  (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ t : Θ, OrbitPacketData (rs t.1)
    (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))
  (hfiber : SemistandardSpectralFiberFinitenessStatement.{u})
  (hmem : GlobalSynthesis.SchwartzMembershipStatement hG a ha muM d rs hindex Q K0 hK0 hKc hPK rho)
  (hspecial : BruhatTits.SpecialCompact.SpecialCompactProperties F i nu
    (K0 : Subgroup (rationalPoints G)))
  (hd : ∀ t, (d t).compact = K0) (hQ : ∀ t, (Q t).compact = K0)

set_option hygiene false in
local notation "degreeZero" =>
  rationalSemistandardDegreeZero a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
    hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ

set_option hygiene false in
local notation "compactK" => (isCompact_iff_compactSpace.mp hKc :
  CompactSpace (K : Subgroup (rationalPoints G)))

variable (hw : letI := compactK
    ConvolutionWeights muG (K : Subgroup (rationalPoints G))
      (rationalXi hKc hPK) (rationalHeight (F := F) rho))

/-- **Lemma VIII.2.3 for the actual operator.** For `f₁` in `rationalCuspidalSubmodule` (the
integrable proper-standard presentation of the cuspidal kernel) and every Schwartz `f₂`,
`f₁ ∗ f₂ = f₁ ∗ °f₂` and `f₂ ∗ f₁ = °f₂ ∗ f₁`, for the Library's Schwartz convolution with the
ambient Haar measure `muG` (integrability and closure from `ConvolutionWeights`). The premises
are the VI.3.1 component continuity target (Schwartz lifts of the packets of the finite sum
`κ(ψ)`) and the vanishing of both convolutions of every element of `rationalCuspidalSubmodule`
with every packet at a proper semistandard index
(`GlobalSynthesis.ProperPacketConvolutionVanishingStatement`). -/
def RationalSemistandardDegreeZeroConvolutionStatement : Prop :=
  letI := compactK
  GlobalSynthesis.ComponentContinuityStatement hG a ha muM d rs hindex Q K0 hKc hPK rho →
    GlobalSynthesis.ProperPacketConvolutionVanishingStatement hG a ha muM d rs hindex Q hKc hPK
      rho muG →
      ∀ f₁ f₂ : Schwartz, f₁ ∈ rationalCuspidalSubmodule hKc hPK rho →
        Space.convolution hw f₁ f₂ = Space.convolution hw f₁ (degreeZero f₂) ∧
        Space.convolution hw f₂ f₁ = Space.convolution hw (degreeZero f₂) f₁

/-- The lift `ψ` of `f₂` is supported on proper indices, so the Library's finite-sum reduction
`GlobalSynthesis.properSynthesisConvolution` applies to `κ(ψ)`. -/
theorem rationalSemistandardDegreeZero_convolution :
    RationalSemistandardDegreeZeroConvolutionStatement a ha muM d hG C hi hnu hKc hPK rho hsw
      hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ
      hw := by
  intro hcont hvanish f₁ f₂ hf₁
  exact GlobalSynthesis.properSynthesisConvolution hG a ha muM d rs hindex Q K0 hK0 hKc hPK rho hw
    hmem hcont hfiber hi hnu hspecial hd hQ hvanish
    (rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov f₂).val
    (rationalSemistandardProperFourierInvariant_support_subset a ha muM d hG C hi hnu hKc hPK rho
      hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov f₂) f₁ f₂ hf₁

include hw in
/-- The left convolution law of `RationalCuspidalUnit` for the operator, under the premises of
`RationalSemistandardDegreeZeroConvolutionStatement`. -/
theorem rationalSemistandardDegreeZero_leftConvolutionLaw
    (hcont : GlobalSynthesis.ComponentContinuityStatement hG a ha muM d rs hindex Q K0 hKc hPK rho)
    (hvanish : GlobalSynthesis.ProperPacketConvolutionVanishingStatement hG a ha muM d rs hindex Q
      hKc hPK rho muG) :
    RationalDegreeZeroLeftConvolutionLaw hKc hPK rho degreeZero muG := by
  intro f₁ hf₁ f₂ x
  have h := (rationalSemistandardDegreeZero_convolution a ha muM d hG C hi hnu hKc hPK rho hsw
    hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hw
    hcont hvanish f₁ f₂ hf₁).1
  exact (congrArg (fun φ : Schwartz => φ x) h).symm

/-! ## The proper-packet vanishing through VII.2 (1) and VII.1.2 -/

/-- **Lemma VIII.2.3 with the packet vanishing reduced to Fourier vanishing.** The vanishing
premise is replaced by the inputs of `GlobalSynthesis.properPacketConvolutionFromFourier`: the
comparison `RationalCuspidalSemistandardComparisonStatement` of `rationalCuspidalSubmodule` with
vanishing of all normalized proper semistandard induced constant terms, closedness of the
matrix representation, the VII.1.2 analytic inputs at each proper index, VII.1.3 component
smoothness at every index, and the product integrability of the VII.2 (1) pairing. The ambient
Haar measure `muG` is the same in the Fourier family defining the operator, in the pairing and
in the convolution. -/
def RationalSemistandardDegreeZeroConvolutionFromFourierStatement [muG.IsInvInvariant] : Prop :=
  letI := compactK
  GlobalSynthesis.ComponentContinuityStatement hG a ha muM d rs hindex Q K0 hKc hPK rho →
    RationalCuspidalSemistandardComparisonStatement.{u} → IsClosedSubgroup rho →
    (∀ t : Θ, t.1.IsProper →
      ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
        muU.IsHaarMeasure ∧
          RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
            t.1 (chosenLeviModel t.1) (d t.1)
            (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
            muL muU XiM sigmaM) →
    (∀ (f : Schwartz) (t : Θ),
      fourier f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t) →
    GlobalSynthesis.ProperPacketConvolutionIntegrabilityStatement hG hi hnu hKc hPK rho a ha muM d
      rs hindex Q muG →
      ∀ f₁ f₂ : Schwartz, f₁ ∈ rationalCuspidalSubmodule hKc hPK rho →
        Space.convolution hw f₁ f₂ = Space.convolution hw f₁ (degreeZero f₂) ∧
        Space.convolution hw f₂ f₁ = Space.convolution hw (degreeZero f₂) f₁

theorem rationalSemistandardDegreeZero_convolution_of_fourier [muG.IsInvInvariant] :
    RationalSemistandardDegreeZeroConvolutionFromFourierStatement a ha muM d hG C hi hnu hKc hPK
      rho hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial
      hd hQ hw := by
  intro hcont hcmp hrho hin' hsm hint
  exact rationalSemistandardDegreeZero_convolution a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
    hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hw hcont
    (GlobalSynthesis.properPacketConvolutionFromFourier hG hi hnu hKc hPK rho a ha muM d rs hindex Q
      hsw hdelta hT hcmp hrho hin' hsm hint)

end Langlands.HarishChandraSchwartz
