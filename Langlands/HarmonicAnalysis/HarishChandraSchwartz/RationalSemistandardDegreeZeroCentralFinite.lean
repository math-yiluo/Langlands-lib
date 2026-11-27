import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardDegreeZeroKernel
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardDegreeZeroSymmetry
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardDegreeZeroConvolution
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalUnitAssembly
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCenterHeightProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound

/-! # Proposition VIII.4.1 at the degree-zero operator `f ↦ °f` of VIII.2

The operator `rationalSemistandardDegreeZero` (`°f = f - κ(ψ)`) satisfies the six degree-zero
laws `IsRationalDegreeZeroOperator` under the premises of Lemma VIII.2.1, Remark VIII.2.2 and
Lemma VIII.2.3 for it. With the special-vertex compact inputs and Corollary VIII.3.2, the
local kernel step of Proposition VIII.4.1 then applies at `°e = °(1_H)`: for the group `G`
carrying the operator, the actual central level span of every compact open `H` equals the raw
central-integral image and is finite dimensional.
-/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
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

local instance degreeZeroCentralCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance degreeZeroCentralParabolicLC (p : SemistandardSpectralIndex i) :
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

local instance degreeZeroCentralLeviAffine {p : SemistandardSpectralIndex i} (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom

local instance degreeZeroCentralLeviFiniteType {p : SemistandardSpectralIndex i}
    (m : LeviModel p) : LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

/-! ## The six degree-zero laws for the operator -/

omit [SFinite muG] in
/-- The range law `°f ∈ rationalCuspidalSubmodule` from the comparison of Lemma VIII.2.1. -/
theorem rationalSemistandardDegreeZero_rangeLaw_of_kernelComparison
    (h : RationalSemistandardDegreeZeroKernelComparison a ha muM d hG C hi hnu hKc hPK rho hsw
      hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ) :
    RationalDegreeZeroRangeLaw hKc hPK rho degreeZero := fun f => by
  rw [← h.1]
  exact LinearMap.mem_range_self _ f

include hw in
/-- **The degree-zero laws for the actual operator.** Under the premises of the conditional
Lemma VIII.2.1 (`RationalSemistandardDegreeZeroKernelStatement`: the VII.2.5 inverse input, the
semistandard constant-term comparison, a closed matrix representation, the VII.1.2 analytic
inputs at the proper indices, outer-Levi data with the change of normalization of every `f^M`,
and synthesis reconstruction in strictly smaller relative semisimple rank), of Remark VIII.2.2
(the induced-character and proper-orbit symmetries) and of Lemma VIII.2.3 (VI.3.1 component
continuity and the proper-packet convolution vanishing for `muG`), the operator `°f = f - κ(ψ)`
satisfies `IsRationalDegreeZeroOperator` for the ambient Haar measure `muG`. -/
theorem rationalSemistandardDegreeZero_isRationalDegreeZeroOperator
    (hinv : RationalSemistandardDegreeZeroInverseInput a ha muM d hG C hi hnu hKc hPK rho hsw
      hdelta hT rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ)
    (hcmp : RationalCuspidalSemistandardComparisonStatement.{u}) (hrho : IsClosedSubgroup rho)
    (hin' : ∀ t : Θ, t.1.IsProper →
      ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
        muU.IsHaarMeasure ∧
          RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
            t.1 (chosenLeviModel t.1) (d t.1)
            (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
            muL muU XiM sigmaM)
    (c : ∀ p : SemistandardSpectralIndex i, p.IsProper →
      RationalSemistandardLeviFourierData.{u, uV} (muG := muG) hKc hPK rho a ha muM d p)
    (src : ∀ (p : SemistandardSpectralIndex i) (hp : p.IsProper),
      RationalSourceFourierData.{u, uV} (c p hp).model.scheme)
    (htr : ∀ (p : SemistandardSpectralIndex i) (hp : p.IsProper) (f : Schwartz)
      (g : rationalPoints G × rationalPoints G),
      RationalSemistandardLeviFourierData.SourceFourierTransferAt a ha muM d hKc hPK rho (c p hp)
        (src p hp) ((c p hp).constantTerm f g))
    (hrec : RationalStrictlyLowerRankSynthesisReconstructionStatement.{u, uV}
      (relativeRootRank i))
    (hchar : SemistandardInducedCharacterSymmetryStatement hG hi hnu hKc hPK rho
      a ha muM d hsw hT)
    (horbit : GlobalSynthesis.ProperOrbitSymmetryStatement a ha muM d hindex hG rs Q)
    (hcont : GlobalSynthesis.ComponentContinuityStatement hG a ha muM d rs hindex Q K0 hKc hPK
      rho)
    (hvanish : GlobalSynthesis.ProperPacketConvolutionVanishingStatement hG a ha muM d rs hindex
      Q hKc hPK rho muG) :
    IsRationalDegreeZeroOperator hKc hPK rho muG degreeZero :=
  ⟨rationalSemistandardDegreeZero_rangeLaw_of_kernelComparison a ha muM d hG C hi hnu hKc hPK rho
      hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd
      hQ (rationalSemistandardDegreeZeroKernel a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
        hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hinv hcmp
        hrho hin' c src htr hrec),
    rationalSemistandardDegreeZero_translationLaw a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ,
    rationalSemistandardDegreeZero_conjLaw a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hchar
      horbit,
    rationalSemistandardDegreeZero_checkLaw a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hchar
      horbit,
    rationalSemistandardDegreeZero_twistLaw a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hchar
      horbit,
    rationalSemistandardDegreeZero_leftConvolutionLaw a ha muM d hG C hi hnu hKc hPK rho hsw
      hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ
      hw hcont hvanish⟩

/-! ## The local VIII.4.1 step at the operator -/

/-- **Proposition VIII.4.1 at the actual degree-zero operator, as a conditional local step.**
For the group `G` with the data of `°f = f - κ(ψ)` (whose construction uses local VIII.1.2 only
in strictly smaller relative semisimple rank, `hlow`), assume the premises of Lemma VIII.2.1
for the operator (among them VIII.1 (2) in strictly smaller rank), those of Remark VIII.2.2 and
of Lemma VIII.2.3, the special-vertex compact inputs and Corollary VIII.3.2. Then the operator
has the degree-zero laws for `muG`, and for every split component `s` of `G`, Haar measure
`muA` on `A_G(F)`, continuous unitary character `χ` and compact open subgroup `H`, the actual
central level span equals the raw central-integral level image and is finite dimensional. -/
def RationalSemistandardDegreeZeroCentralFiniteStatement : Prop :=
  RationalSemistandardDegreeZeroInverseInput a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ →
    RationalCuspidalSemistandardComparisonStatement.{u} → IsClosedSubgroup rho →
    (∀ t : Θ, t.1.IsProper →
      ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
        muU.IsHaarMeasure ∧
          RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
            t.1 (chosenLeviModel t.1) (d t.1)
            (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
            muL muU XiM sigmaM) →
    ∀ (c : ∀ p : SemistandardSpectralIndex i, p.IsProper →
        RationalSemistandardLeviFourierData.{u, uV} (muG := muG) hKc hPK rho a ha muM d p)
      (src : ∀ (p : SemistandardSpectralIndex i) (hp : p.IsProper),
        RationalSourceFourierData.{u, uV} (c p hp).model.scheme),
      (∀ (p : SemistandardSpectralIndex i) (hp : p.IsProper) (f : Schwartz)
        (g : rationalPoints G × rationalPoints G),
        RationalSemistandardLeviFourierData.SourceFourierTransferAt a ha muM d hKc hPK rho
          (c p hp) (src p hp) ((c p hp).constantTerm f g)) →
      RationalStrictlyLowerRankSynthesisReconstructionStatement.{u, uV} (relativeRootRank i) →
      SemistandardInducedCharacterSymmetryStatement hG hi hnu hKc hPK rho a ha muM d hsw hT →
      GlobalSynthesis.ProperOrbitSymmetryStatement a ha muM d hindex hG rs Q →
      GlobalSynthesis.ComponentContinuityStatement hG a ha muM d rs hindex Q K0 hKc hPK rho →
      GlobalSynthesis.ProperPacketConvolutionVanishingStatement hG a ha muM d rs hindex Q hKc hPK
        rho muG →
      (letI := compactK; ConvolutionWeights muG (K : Subgroup (rationalPoints G))
          (rationalXi hKc hPK) (rationalHeight (F := F) rho)) →
      CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u} →
      RationalCuspidalConjugationIntegrabilityStatement.{u} →
        IsRationalDegreeZeroOperator hKc hPK rho muG degreeZero ∧
        ∀ (Z : CommGroupScheme (Spec (CommRingCat.of F))) (s : Z.toGrp ⟶ G),
          IsSplitComponent s →
        ∀ (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
          (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
        ∀ H : OpenSubgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
          (rationalCuspidalCentralLevelSpan hKc hPK rho muA χ H.toSubgroup :
            Set (rationalPoints G → ℂ)) =
              rationalCuspidalCentralLevelImage hKc hPK rho muA χ H.toSubgroup ∧
          FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK rho muA χ H.toSubgroup)

/-- The local step: the laws come from `rationalSemistandardDegreeZero_isRationalDegreeZeroOperator`,
and the conclusion of Proposition VIII.4.1 from
`IsRationalDegreeZeroOperator.centralLevelSpan_eq_image_and_finiteDimensional` with the proved
split-centre heights `rationalSplitCenterHeight` and Lemma II.1.5 in the form
`rationalXiSquareIntegrable_of_upperBound rationalXiUpperBound`. -/
theorem rationalSemistandardDegreeZeroCentralFinite :
    RationalSemistandardDegreeZeroCentralFiniteStatement a ha muM d hG C hi hnu hKc hPK rho hsw
      hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd
      hQ := by
  intro hinv hcmp hrho hin' c src htr hrec hchar horbit hcont hvanish hw hSV h32
  have hP := rationalSemistandardDegreeZero_isRationalDegreeZeroOperator a ha muM d hG C hi hnu
    hKc hPK rho hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem
    hspecial hd hQ hw hinv hcmp hrho hin' c src htr hrec hchar horbit hcont hvanish
  refine ⟨hP, ?_⟩
  intro Z s hs muA _ χ hχc hχ H hHc
  exact hP.centralLevelSpan_eq_image_and_finiteDimensional hKc hPK rho rationalSplitCenterHeight
    (rationalXiSquareIntegrable_of_upperBound rationalXiUpperBound) hSV h32 hG hi hnu hrho hs muA
    χ hχc hχ H hHc

end Langlands.HarishChandraSchwartz
