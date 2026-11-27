import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardDegreeZero
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierDetection
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierReconstruction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSynthesisInverse

/-! # Lemma VIII.2.1: the range of the degree-zero operator -/

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

local instance degreeZeroKernelCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance degreeZeroKernelParabolicLC (p : SemistandardSpectralIndex i) :
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
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
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
local notation "kappa" =>
  GlobalSynthesis.invariantSynthesis hG a ha muM d rs hindex Q K0 hK0 C hi hfiber hKc hPK rho
    hmem hnu hspecial hd hQ

set_option hygiene false in
local notation "lift" =>
  rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
    hgeo hcomp hlow hS hin hsplit hcov

/-! ## The elementary projector algebra -/

section Projector

/-- The VII.2.5 inverse identity at the fixed inputs of the operator, in the product form:
the actual Fourier family of `κ(ψ)` is `ψ`, for every element `ψ` of the invariant carrier. -/
abbrev RationalSemistandardDegreeZeroInverseInput : Prop :=
  ∀ psi : rationalSemistandardThetaInvariantSections C,
    fourier (kappa psi) = rationalSemistandardThetaInvariantInclusion C psi

variable (hinv : RationalSemistandardDegreeZeroInverseInput a ha muM d hG C hi hnu hKc hPK rho hsw
  hdelta hT rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ)

include hinv

/-- The proper truncation of `κ(ψ)` is the proper part of `ψ`. -/
theorem rationalSemistandardProperFourier_invariantSynthesis
    (psi : rationalSemistandardThetaInvariantSections C) :
    properFourier (kappa psi) = properPart psi.val.val := by
  change properPart (fourier (kappa psi)) = _
  rw [hinv psi]
  rfl

/-- **The image has zero proper Fourier components:** the proper truncation of `°f` is zero. -/
theorem rationalSemistandardProperFourier_degreeZero (f : Schwartz) :
    properFourier (degreeZero f) = 0 := by
  rw [rationalSemistandardDegreeZero_apply, map_sub,
    rationalSemistandardProperFourier_invariantSynthesis a ha muM d hG C hi hnu hKc hPK rho hsw
      hdelta hT rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hinv,
    rationalSemistandardProperFourierInvariant_val_val]
  change properPart (fourier f) - properPart (properPart (fourier f)) = 0
  rw [rationalSemistandardThetaProperPart_idem, sub_self]

/-- Fixed points are exactly the functions with zero proper truncation. -/
theorem rationalSemistandardDegreeZero_eq_self_iff (f : Schwartz) :
    degreeZero f = f ↔ properFourier f = 0 := by
  constructor
  · intro h
    rw [← h]
    exact rationalSemistandardProperFourier_degreeZero a ha muM d hG C hi hnu hKc hPK rho hsw
      hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ
      hinv f
  · exact rationalSemistandardDegreeZero_eq_self_of_properFourier_eq_zero a ha muM d hG C hi hnu
      hKc hPK rho hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem
      hspecial hd hQ f

/-- **Idempotence:** `°(°f) = °f`. -/
theorem rationalSemistandardDegreeZero_idem (f : Schwartz) :
    degreeZero (degreeZero f) = degreeZero f :=
  (rationalSemistandardDegreeZero_eq_self_iff a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
    hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hinv _).mpr
    (rationalSemistandardProperFourier_degreeZero a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hinv f)

/-- The range is the set of fixed points. -/
theorem rationalSemistandardDegreeZero_mem_range_iff (f : Schwartz) :
    f ∈ LinearMap.range degreeZero ↔ degreeZero f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact rationalSemistandardDegreeZero_idem a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hinv g
  · intro h
    exact ⟨f, h⟩

/-- The range is the kernel of the proper truncation. -/
theorem rationalSemistandardDegreeZero_range_eq_ker :
    LinearMap.range degreeZero = LinearMap.ker properFourier := by
  ext f
  rw [rationalSemistandardDegreeZero_mem_range_iff a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
    hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hinv,
    LinearMap.mem_ker]
  exact rationalSemistandardDegreeZero_eq_self_iff a ha muM d hG C hi hnu hKc hPK rho hsw hdelta
    hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hinv f

end Projector

/-! ## The forward direction: identity on the intrinsic kernel -/

/-- **The operator is the identity on the intrinsic cuspidal kernel.** If every proper
semistandard induced constant term of `f` vanishes, VII.1.2 makes every proper Fourier
component of `f` zero (`rationalSemistandardCuspidalProperFourierVanishing`), so the lift of `f`
is zero and `°f = f`. This direction uses neither VII.2.5 nor reconstruction. -/
theorem rationalSemistandardDegreeZero_eq_self_of_mem_cuspidal
    (hcmp : RationalCuspidalSemistandardComparisonStatement.{u}) (hrho : IsClosedSubgroup rho)
    (hin' : ∀ t : Θ, t.1.IsProper →
      ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
        muU.IsHaarMeasure ∧
          RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
            t.1 (chosenLeviModel t.1) (d t.1)
            (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
            muL muU XiM sigmaM)
    (f : Schwartz) (hf : f ∈ rationalCuspidalSubmodule hKc hPK rho) : degreeZero f = f :=
  rationalSemistandardDegreeZero_eq_self_of_properFourier_eq_zero a ha muM d hG C hi hnu hKc hPK
    rho hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd
    hQ f ((rationalSemistandardProperFourier_eq_zero_iff hG hi hnu hKc hPK rho hsw a ha muM d
      hdelta hT f).mpr
        (rationalSemistandardCuspidalProperFourierVanishing hG hi hnu hKc hPK rho hsw a ha muM d
          hdelta hT hcmp hrho hin' f hf))

/-! ## The comparison of Lemma VIII.2.1 -/

/-- **The conclusion of Lemma VIII.2.1** for the actual operator: its range, its fixed points,
the vanishing of all proper Fourier components and the intrinsic kernel `rationalCuspidalSubmodule`
(vanishing of every proper semistandard induced constant term) agree. -/
def RationalSemistandardDegreeZeroKernelComparison : Prop :=
  LinearMap.range degreeZero = rationalCuspidalSubmodule hKc hPK rho ∧
    (∀ f : Schwartz, degreeZero f = f ↔ f ∈ rationalCuspidalSubmodule hKc hPK rho) ∧
    LinearMap.ker properFourier = rationalCuspidalSubmodule hKc hPK rho

/-- The comparison follows from the inverse input and the Fourier/constant-term detection
`ker properFourier = rationalCuspidalSubmodule`, by the projector algebra above. -/
theorem rationalSemistandardDegreeZeroKernelComparison_of_detection
    (hinv : RationalSemistandardDegreeZeroInverseInput a ha muM d hG C hi hnu hKc hPK rho hsw
      hdelta hT rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ)
    (hdetect : LinearMap.ker properFourier = rationalCuspidalSubmodule hKc hPK rho) :
    RationalSemistandardDegreeZeroKernelComparison a ha muM d hG C hi hnu hKc hPK rho hsw hdelta
      hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ := by
  refine ⟨?_, fun f => ?_, hdetect⟩
  · rw [rationalSemistandardDegreeZero_range_eq_ker a ha muM d hG C hi hnu hKc hPK rho hsw hdelta
      hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hinv,
      hdetect]
  · rw [rationalSemistandardDegreeZero_eq_self_iff a ha muM d hG C hi hnu hKc hPK rho hsw hdelta
      hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ hinv,
      ← LinearMap.mem_ker, hdetect]

/-! ## Fourier/constant-term detection -/

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- **Detection assuming Fourier injectivity at the outer-Levi data.** Given, at every proper
index, the actual outer-Levi data of `RationalSemistandardLeviFourierData` (a closed connected
reductive model of the literal Levi, the actual Schwartz function
`f^M = f^{(P,Ind)}(g₁,g₂)` pulled back to it, the nested VII.1.2/III.6 coverage with the
factors `δ_P(m₁)^{-1/2} δ_P(m₂)^{-1/2}`), and, as a direct premise, injectivity of the Fourier
family of each such Levi model at those outer-Levi data, the kernel of the proper truncation is
the intrinsic cuspidal kernel. This is an auxiliary reduction; the target uses
`rationalSemistandardProperFourier_ker_eq_cuspidal_of_lowerRankReconstruction`. -/
theorem rationalSemistandardProperFourier_ker_eq_cuspidal
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
    (hzero : ∀ p hp, ∀ fM, (c p hp).fourier fM = 0 → fM = 0) :
    LinearMap.ker properFourier = rationalCuspidalSubmodule hKc hPK rho := by
  ext f
  rw [LinearMap.mem_ker]
  exact rationalSemistandardProperFourier_eq_zero_iff_mem_cuspidal hG hi hnu hsw hdelta hT hcmp
    hrho hin' c (fun p hp _ => hzero p hp) f

local instance degreeZeroKernelLeviAffine {p : SemistandardSpectralIndex i} (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom

local instance degreeZeroKernelLeviFiniteType {p : SemistandardSpectralIndex i} (m : LeviModel p) :
    LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

namespace RationalSemistandardLeviFourierData

attribute [local instance] ambientHaar_haar ambientHaar_right centerNormal quotientMeasurable
  quotientBorel quotientHaar_haar quotientHaar_inv

omit [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant] [∀ t, IsAffine (T t).X.left]
  [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- **Local Fourier injectivity at the data of `c` detects zero on its Levi Schwartz space.**
`FourierInversion.RationalLocalFourierInjectivityStatement` for the Levi model, specialized to
the Fourier data carried by `c`, gives `fM = 0` for every Schwartz function `fM` on that model
with zero Fourier family at those data. This is used only by the auxiliary injectivity route. -/
theorem eq_zero_of_fourier_eq_zero {p : SemistandardSpectralIndex i}
    (c : RationalSemistandardLeviFourierData.{u, uV} (muG := muG) hKc hPK rho a ha muM d p)
    (h : RationalSemistandard.FourierInversion.RationalLocalFourierInjectivityStatement.{u, uV}
      c.model.scheme)
    (fM : RationalSchwartzSpace c.compact_isCompact c.iwasawa (rho.restrict c.model.inclusion))
    (hfM : c.fourier fM = 0) : fM = 0 :=
  h c.model.reductive c.torus c.iM c.maximal c.nuM c.generic c.compact c.compact_isCompact
    c.iwasawa N (rho.restrict c.model.inclusion) c.ambientHaar c.squareIntegrableWeight
    c.splitCenterTorus c.splitCenterInclusion c.splitComponent c.quotientHaar c.compactData
    c.normalization c.tempered fM hfM

end RationalSemistandardLeviFourierData

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- **Auxiliary reduction: strictly lower-rank Fourier injectivity at arbitrary data implies the
outer-Levi detection premise by `semistandardProperLeviRank`.** Injectivity of the Fourier
family for every connected reductive group of relative semisimple rank strictly below that of
`G`, at arbitrary Fourier data
(`FourierInversion.RationalStrictlyLowerRankFourierInjectivityStatement`), applies to the closed
reductive model of each proper Levi, whose rank is smaller by `semistandardProperLeviRank`, at
the Fourier data of `RationalSemistandardLeviFourierData`; it detects `f^M = 0`. This premise
is not the source's formula (2), which is stated at source-normalized data; the target below
uses lower-rank synthesis reconstruction instead. -/
theorem rationalSemistandardProperFourier_ker_eq_cuspidal_of_lowerRankInjectivity
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
    (hinj : RationalSemistandard.FourierInversion.RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV}
      (relativeRootRank i)) :
    LinearMap.ker properFourier = rationalCuspidalSubmodule hKc hPK rho := by
  refine rationalSemistandardProperFourier_ker_eq_cuspidal a ha muM d hG hi hnu hKc hPK rho hsw
    hdelta hT hcmp hrho hin' c ?_
  intro p hp fM hfM
  exact RationalSemistandardLeviFourierData.eq_zero_of_fourier_eq_zero a ha muM d hKc hPK rho (c p hp)
    (RationalSemistandard.FourierInversion.rationalLocalFourierInjectivity_properLevi_of_lowerRank
      hG hi hinj p hp (c p hp).model) fM hfM

/-! ## Strictly lower-rank reconstruction in the form `κ(ψ_f) = f` -/

omit [∀ t, (muM t).IsInvInvariant] [∀ t, IsAffine (T t).X.left]
  [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- A vanishing family is Weyl invariant: every fiber comparison is linear. -/
theorem isWeylInvariant_zero : IsWeylInvariant C 0 :=
  fun t q n A => (C.fiberComparison t q n A).map_zero.symm

/-- **The `κ` form of VIII.1 (2) contains its zero case**, at fixed data: if `κ(ψ_f) = f` for
every Schwartz function whose Fourier family lies in `C^∞(Θ)_inv`, then a Schwartz function
with vanishing Fourier family is zero. Its family is the zero element of `C^∞(Θ)_inv`, whose
synthesis is zero. -/
theorem fourierInjectivity_of_synthesisReconstruction
    (Q0 : ∀ t : Θ, OrbitPacketData (C.presentation t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2))
    (hmem0 : GlobalSynthesis.SchwartzMembershipStatement hG a ha muM d C.presentation hindex Q0
      K0 hK0 hKc hPK rho)
    (hQ0 : ∀ t, (Q0 t).compact = K0)
    (h : RationalSemistandard.FourierInversion.SynthesisReconstructionStatement hG hi hnu hKc hPK
      rho hsw a ha muM d hdelta hT C hindex Q0 K0 hK0 hmem0 hspecial hd hQ0) :
    RationalSemistandard.FourierInversion.FourierInjectivityStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT := by
  intro f hf
  have hm : RationalSemistandard.FourierInversion.FourierInvariantMembership hG hi hnu hKc hPK
      rho hsw a ha muM d hdelta hT C f := by
    refine ⟨?_, ?_⟩
    · rw [hf]
      exact Submodule.zero_mem _
    · rw [hf]
      exact isWeylInvariant_zero a ha muM d hG C
  have hlift : RationalSemistandard.FourierInversion.fourierInvariantLift hG hi hnu hKc hPK rho
      hsw a ha muM d hdelta hT C f hm = 0 :=
    Subtype.ext (Subtype.ext hf)
  have h0 := h f hm
  rw [hlift, map_zero] at h0
  exact h0.symm

/-- VIII.1 (2) in the form `κ(ψ_f) = f` (`FourierInversion.RationalLocalSynthesisReconstructionStatement`)
for every actual connected reductive group of relative semisimple rank strictly below `n`,
measured with a maximal split torus. It names only lower-rank groups and contains no
finiteness assertion. -/
def RationalStrictlyLowerRankSynthesisReconstructionStatement (n : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    relativeRootRank i < n →
      RationalSemistandard.FourierInversion.RationalLocalSynthesisReconstructionStatement.{u, uV} G

/-- Increasing the strict rank bound adds requirements. -/
theorem rationalStrictlyLowerRankSynthesisReconstruction_mono {n m : ℕ} (hnm : n ≤ m)
    (h : RationalStrictlyLowerRankSynthesisReconstructionStatement.{u, uV} m) :
    RationalStrictlyLowerRankSynthesisReconstructionStatement.{u, uV} n := by
  intro F _ _ _ _ G _ _ hG T i hi hlt
  exact h F G hG T i hi (lt_of_lt_of_le hlt hnm)

/-- There is no group of relative semisimple rank strictly below zero. -/
theorem rationalStrictlyLowerRankSynthesisReconstruction_zero :
    RationalStrictlyLowerRankSynthesisReconstructionStatement.{u, uV} 0 := by
  intro F _ _ _ _ G _ _ hG T i hi hlt
  exact (Nat.not_lt_zero _ hlt).elim

/-- The unquotiented lower-rank formula gives the `κ` form, groupwise by
`FourierInversion.rationalLocalSynthesisReconstruction_of_unquotiented`. -/
theorem rationalStrictlyLowerRankSynthesisReconstruction_of_unquotiented {n : ℕ}
    (h : RationalSemistandard.FourierInversion.RationalStrictlyLowerRankUnquotientedReconstructionStatement.{u, uV} n) :
    RationalStrictlyLowerRankSynthesisReconstructionStatement.{u, uV} n := by
  intro F _ _ _ _ G _ _ hG T i hi hlt
  exact RationalSemistandard.FourierInversion.rationalLocalSynthesisReconstruction_of_unquotiented
    (h F G hG T i hi hlt)

omit [LocallyOfFiniteType G.X.hom] in
include hG hi in
/-- Every closed reductive model of a literal proper semistandard Levi lies within the strict-rank
premise at the rank of `G`, by the proved rank decrease `semistandardProperLeviRank` and the
inherited maximal split torus. No assertion for `G` itself occurs. -/
theorem rationalLocalSynthesisReconstruction_properLevi_of_lowerRank
    (h : RationalStrictlyLowerRankSynthesisReconstructionStatement.{u, uV} (relativeRootRank i))
    (p : SemistandardSpectralIndex i) (hp : p.parabolic ≠ ⊤)
    (m : RationalSemistandard.LeviModel p) :
    haveI := m.reductive.isAffineHom
    haveI := m.reductive.smooth
    RationalSemistandard.FourierInversion.RationalLocalSynthesisReconstructionStatement.{u, uV}
      m.scheme := by
  let := m.reductive.isAffineHom
  let : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
  let := m.reductive.smooth
  exact h F m.scheme m.reductive S
    (semistandardLeviSplitTorus p m.represents)
    (isMaximalSplitTorus_semistandardLeviSplitTorus p m.represents m.closed hi)
    (semistandardProperLeviRank F G hG S i hi p hp m.scheme m.inclusion m.represents m.closed
      m.reductive)

/-! ## Source-normalized data on a lower-rank group -/

section SourceData

/-- **Source-normalized Fourier and synthesis data on a group `H`**, with the conventions of
I.1 and VII.2.5 under which `FourierInversion.RationalLocalSynthesisReconstructionStatement H`
asserts `κ(ψ_f) = f`: a maximal split torus with a generic cocharacter; one compact open
subgroup `compact` serving as source special compact (`IsSourceCompactAt`), as Iwasawa compact
of the Schwartz space, as compact of every compact picture and as compact of every packet; a
closed matrix embedding with `compact` in its integral height subgroup; the ambient Haar
measure `RationalDynamicSource.ambientHaar compact _` of mass one on `compact`; split-central
quotient Haar measures normalized as in I.1 (`SourceLeviQuotientHaar`); the Weyl comparison
data with their presentations, packet data and Schwartz membership of the weighted packets.
The fields are exactly the data and hypotheses over which the local reconstruction target is
quantified. -/
structure RationalSourceFourierData (H : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] where
  reductive : IsConnectedReductive H
  torus : CommGroupScheme (Spec (CommRingCat.of F))
  iT : torus.toGrp ⟶ H
  maximal : IsMaximalSplitTorus iT
  nuT : cocharacterLattice torus
  generic : IsGenericCocharacter iT nuT
  compact : OpenSubgroup (rationalPoints H)
  compact_isCompact : IsCompact (compact : Set (rationalPoints H))
  iwasawa : IsIwasawaPair (standardParabolicPoints iT nuT ∅) (compact : Subgroup (rationalPoints H))
  dim : ℕ
  [dim_nonempty : Nonempty (Fin dim)]
  embedding : MatrixRepresentation H (Fin dim)
  embedding_closed : IsClosedSubgroup embedding
  compact_le_height :
    (compact : Subgroup (rationalPoints H)) ≤ rationalHeightSubgroup (F := F) embedding
  centerTorus : SemistandardSpectralIndex iT → CommGroupScheme (Spec (CommRingCat.of F))
  [centerTorus_affine : ∀ t, IsAffine (centerTorus t).X.left]
  centerInclusion : ∀ t, (centerTorus t).toGrp ⟶ (chosenLeviModel t).scheme
  splitComponent : ∀ t, IsSplitComponent (centerInclusion t)
  [centerNormal : ∀ t, ((chosenLeviModel t).splitCenter (centerInclusion t)).Normal]
  [rangeNormal : ∀ t, (rationalPoints.map (centerInclusion t)).range.Normal]
  [quotientMeasurable : ∀ t,
    MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (centerInclusion t))]
  [quotientBorel : ∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (centerInclusion t))]
  quotientHaar : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (centerInclusion t))
  [quotientHaar_haar : ∀ t, (quotientHaar t).IsHaarMeasure]
  [quotientHaar_inv : ∀ t, (quotientHaar t).IsInvInvariant]
  compactData : ∀ t : SemistandardSpectralIndex iT, CompactData t
  normalization : ∀ t : SemistandardSpectralIndex iT, ModularNormalization t
  tempered : ∀ (t : SemistandardSpectralIndex iT)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel t).splitCenter (centerInclusion t))
      ((chosenLeviModel t).splitCenter_le_center (centerInclusion t) (splitComponent t))
      A.obj.representation (quotientHaar t) →
    HasTemperedCoefficients (rationalXi compact_isCompact iwasawa)
      (rationalHeight (F := F) embedding)
      ((normalizedInductionFunctor (decomposition t) (isClosed_radical t)).obj A.obj).representation
  squareIntegrableWeight :
    SquareIntegrableWeight (RationalDynamicSource.ambientHaar compact compact_isCompact)
      (rationalXi compact_isCompact iwasawa) (rationalHeight (F := F) embedding)
  comparison : WeylSectionComparisonData.{u, uV} centerInclusion splitComponent quotientHaar
    compactData reductive
  finiteIndex : ∀ t, (RenardCartan.splitValuationImage (centerInclusion t)).FiniteIndex
  packets : ∀ theta : RationalSemistandardTheta.{u, uV} centerInclusion splitComponent quotientHaar,
    OrbitPacketData (comparison.presentation theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (centerInclusion theta.1)
        (splitComponent theta.1) (quotientHaar theta.1) theta.2)
  schwartzMembership : GlobalSynthesis.SchwartzMembershipStatement reductive centerInclusion
    splitComponent quotientHaar compactData comparison.presentation finiteIndex packets compact
    compact_isCompact compact_isCompact iwasawa embedding
  special : BruhatTits.SpecialCompact.SpecialCompactProperties F iT nuT
    (compact : Subgroup (rationalPoints H))
  compactData_compact : ∀ t, (compactData t).compact = compact
  packets_compact : ∀ theta, (packets theta).compact = compact
  sourceCompact : Plancherel.WaldspurgerSourceNormalization.IsSourceCompactAt iT compact.toSubgroup
  sourceQuotientHaar : ∀ t, WavePacketPairing.SourceLeviQuotientHaar centerInclusion quotientHaar
    (K := compact) t

namespace RationalSourceFourierData

attribute [local instance] dim_nonempty centerTorus_affine centerNormal rangeNormal
  quotientMeasurable quotientBorel quotientHaar_haar quotientHaar_inv

variable {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  [LocallyOfFiniteType H.X.hom] (s : RationalSourceFourierData.{u, uV} H)

/-- The Harish-Chandra Schwartz space of `H` at the source-normalized data. -/
abbrev SchwartzSpace : Type u :=
  RationalSchwartzSpace s.compact_isCompact s.iwasawa s.embedding

/-- The full Fourier family of `H` at the source-normalized data, for the ambient Haar measure
of mass one on the source compact. -/
def fourierFamily : s.SchwartzSpace →ₗ[ℂ]
    RationalSemistandardThetaSections.{u, uV} s.centerInclusion s.splitComponent s.quotientHaar :=
  haveI := RationalSemistandard.FourierInversion.sourceAmbientHaar_isMulRightInvariant s.reductive
    s.compact_isCompact
  rationalSemistandardFourierFamily s.reductive s.maximal s.generic s.compact_isCompact s.iwasawa
    s.embedding s.squareIntegrableWeight s.centerInclusion s.splitComponent s.quotientHaar
    s.compactData s.normalization s.tempered

/-- **The zero case of local synthesis reconstruction at source-normalized data.** If
`κ(ψ_f) = f` holds on `H` for all source-normalized data
(`FourierInversion.RationalLocalSynthesisReconstructionStatement H`), then at the data `s` a
Schwartz function with vanishing Fourier family is zero
(`fourierInjectivity_of_synthesisReconstruction`). -/
theorem eq_zero_of_fourier_eq_zero
    (h : RationalSemistandard.FourierInversion.RationalLocalSynthesisReconstructionStatement.{u, uV}
      H)
    (f : s.SchwartzSpace) (hf : s.fourierFamily f = 0) : f = 0 := by
  have := RationalSemistandard.FourierInversion.sourceAmbientHaar_isMulRightInvariant s.reductive
    s.compact_isCompact
  exact fourierInjectivity_of_synthesisReconstruction (a := s.centerInclusion)
    (ha := s.splitComponent) (muM := s.quotientHaar) (d := s.compactData) (hG := s.reductive)
    (C := s.comparison) (hi := s.maximal) (hnu := s.generic) (hKc := s.compact_isCompact)
    (hPK := s.iwasawa) (rho := s.embedding) (hsw := s.squareIntegrableWeight)
    (hdelta := s.normalization) (hT := s.tempered) (hindex := s.finiteIndex) (K0 := s.compact)
    (hK0 := s.compact_isCompact) (hspecial := s.special) (hd := s.compactData_compact)
    (Q0 := s.packets) (hmem0 := s.schwartzMembership) (hQ0 := s.packets_compact)
    (h s.reductive s.torus s.iT s.maximal s.nuT s.generic s.compact s.compact_isCompact s.iwasawa
      s.dim s.embedding s.embedding_closed s.compact_le_height s.centerTorus s.centerInclusion
      s.splitComponent s.quotientHaar s.compactData s.normalization s.tempered
      s.squareIntegrableWeight s.comparison s.finiteIndex s.packets s.schwartzMembership s.special
      s.compactData_compact s.packets_compact s.sourceCompact s.sourceQuotientHaar) f hf

end RationalSourceFourierData

end SourceData

/-! ## Detection through lower-rank synthesis reconstruction of `f^M` -/

namespace RationalSemistandardLeviFourierData

attribute [local instance] ambientHaar_haar ambientHaar_right centerNormal quotientMeasurable
  quotientBorel quotientHaar_haar quotientHaar_inv

/-- **The change of normalization on the Levi for one function.** For a Schwartz function `fM`
on the closed Levi model of `c` (Iwasawa compact `c.compact`, Haar measure `c.ambientHaar`,
quotient Haar measures `c.quotientHaar`, the restriction of `rho`) and source-normalized data
`s` on the same group: if the Fourier family of `fM` at the data of `c` vanishes, then the same
function on `M(F)` lies in the Schwartz space of `s` and its Fourier family at `s` vanishes.
Waldspurger works on `M` with the inherited compact `M ∩ K` and compatible Haar measures (I.1),
so the source needs no such step; here the two data are supplied independently, and this
premise records the transfer for the same function. -/
def SourceFourierTransferAt {p : SemistandardSpectralIndex i}
    (c : RationalSemistandardLeviFourierData.{u, uV} (muG := muG) hKc hPK rho a ha muM d p)
    (s : RationalSourceFourierData.{u, uV} c.model.scheme)
    (fM : RationalSchwartzSpace c.compact_isCompact c.iwasawa (rho.restrict c.model.inclusion)) :
    Prop :=
  c.fourier fM = 0 →
    ∃ fM' : s.SchwartzSpace,
      (fM' : rationalPoints c.model.scheme → ℂ) = fM ∧ s.fourierFamily fM' = 0

omit [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant] [∀ t, IsAffine (T t).X.left]
  [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- **Formula (2) on the Levi detects `fM = 0`.** Local synthesis reconstruction on the Levi
model, the change of normalization for `fM`, and the vanishing of the Fourier family of `fM` at
the data of `c` give `fM = 0`: the same function is zero in the source-normalized Schwartz
space by `RationalSourceFourierData.eq_zero_of_fourier_eq_zero`. -/
theorem eq_zero_of_sourceReconstruction {p : SemistandardSpectralIndex i}
    (c : RationalSemistandardLeviFourierData.{u, uV} (muG := muG) hKc hPK rho a ha muM d p)
    (s : RationalSourceFourierData.{u, uV} c.model.scheme)
    (h : RationalSemistandard.FourierInversion.RationalLocalSynthesisReconstructionStatement.{u, uV}
      c.model.scheme)
    {fM : RationalSchwartzSpace c.compact_isCompact c.iwasawa (rho.restrict c.model.inclusion)}
    (htr : SourceFourierTransferAt a ha muM d hKc hPK rho c s fM) (hfM : c.fourier fM = 0) :
    fM = 0 := by
  obtain ⟨fM', hfun, hzero⟩ := htr hfM
  have h0 : fM' = 0 := s.eq_zero_of_fourier_eq_zero h fM' hzero
  ext x
  rw [← hfun, h0]
  rfl

end RationalSemistandardLeviFourierData

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- **Detection from strictly lower-rank synthesis reconstruction, applied to `f^M`.** Let `f`
have zero proper Fourier truncation. For a proper index `p` and a translating pair `g`, the
actual Schwartz function `f^M = f^{(P,Ind)}(g₁,g₂)` on the closed Levi model of `c p` has zero
Fourier family at the data of `c p` (VII.1.2 on both groups and the III.6 transitivity, with
the factors `δ_P(m₁)^{-1/2} δ_P(m₂)^{-1/2}`, in
`RationalSemistandardLeviFourierData.fourier_constantTerm_eq_zero`). The change of
normalization carries `f^M` and this vanishing to the source-normalized data `s p`. The Levi
model has relative semisimple rank below that of `G` (`semistandardProperLeviRank`), so
VIII.1 (2) in the form `κ(ψ_{f^M}) = f^M` holds there, and the zero family gives `f^M = 0`.
Vanishing of all `f^M` is membership in `rationalCuspidalSubmodule`. Conversely, VII.1.2 gives
zero proper truncation on `rationalCuspidalSubmodule`. -/
theorem rationalSemistandardProperFourier_ker_eq_cuspidal_of_lowerRankReconstruction
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
    (s : ∀ (p : SemistandardSpectralIndex i) (hp : p.IsProper),
      RationalSourceFourierData.{u, uV} (c p hp).model.scheme)
    (htr : ∀ (p : SemistandardSpectralIndex i) (hp : p.IsProper) (f : Schwartz)
      (g : rationalPoints G × rationalPoints G),
      RationalSemistandardLeviFourierData.SourceFourierTransferAt a ha muM d hKc hPK rho (c p hp)
        (s p hp) ((c p hp).constantTerm f g))
    (hrec : RationalStrictlyLowerRankSynthesisReconstructionStatement.{u, uV}
      (relativeRootRank i)) :
    LinearMap.ker properFourier = rationalCuspidalSubmodule hKc hPK rho := by
  ext f
  rw [LinearMap.mem_ker]
  constructor
  · intro hf
    apply rationalCuspidal_of_properLeviConstantTerms_eq_zero hG hi hnu hcmp hrho c f
    intro p hp g
    exact RationalSemistandardLeviFourierData.eq_zero_of_sourceReconstruction a ha muM d hKc hPK
      rho (c p hp) (s p hp)
      (rationalLocalSynthesisReconstruction_properLevi_of_lowerRank hG hi hrec p hp (c p hp).model)
      (htr p hp f g)
      ((c p hp).fourier_constantTerm_eq_zero hG hi hnu hsw hdelta hT hp f g hf)
  · intro hf
    exact (rationalSemistandardProperFourier_eq_zero_iff hG hi hnu hKc hPK rho hsw a ha muM d
      hdelta hT f).mpr
        (rationalSemistandardCuspidalProperFourierVanishing hG hi hnu hKc hPK rho hsw a ha muM d
          hdelta hT hcmp hrho hin' f hf)

/-- **Lemma VIII.2.1 for the actual operator, as a conditional target.** Under the VII.2.5
inverse identity at the operator's data (`RationalSemistandardDegreeZeroInverseInput`), the
comparison of `rationalCuspidalSubmodule` with all proper semistandard induced constant terms
for a closed matrix representation, the VII.1.2 analytic inputs at every proper index, the
outer-Levi data of each proper index (the Schwartz function `f^M`, the nested VII.1.2/III.6
coverage), source-normalized data on each such Levi model with the change of normalization for
every `f^M`, and VIII.1 (2) in the form `κ(ψ_f) = f` for all groups of strictly smaller relative
semisimple rank, the range of the operator, its fixed points, the kernel of the proper
truncation and `rationalCuspidalSubmodule` agree. -/
def RationalSemistandardDegreeZeroKernelStatement : Prop :=
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
      (s : ∀ (p : SemistandardSpectralIndex i) (hp : p.IsProper),
        RationalSourceFourierData.{u, uV} (c p hp).model.scheme),
      (∀ (p : SemistandardSpectralIndex i) (hp : p.IsProper) (f : Schwartz)
        (g : rationalPoints G × rationalPoints G),
        RationalSemistandardLeviFourierData.SourceFourierTransferAt a ha muM d hKc hPK rho
          (c p hp) (s p hp) ((c p hp).constantTerm f g)) →
      RationalStrictlyLowerRankSynthesisReconstructionStatement.{u, uV} (relativeRootRank i) →
      RationalSemistandardDegreeZeroKernelComparison a ha muM d hG C hi hnu hKc hPK rho hsw hdelta
        hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ

/-- The target follows from the projector algebra and the detection through lower-rank
synthesis reconstruction. -/
theorem rationalSemistandardDegreeZeroKernel :
    RationalSemistandardDegreeZeroKernelStatement a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ := by
  intro hinv hcmp hrho hin' c s htr hrec
  exact rationalSemistandardDegreeZeroKernelComparison_of_detection a ha muM d hG C hi hnu hKc hPK
    rho hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd
    hQ hinv (rationalSemistandardProperFourier_ker_eq_cuspidal_of_lowerRankReconstruction a ha muM
      d hG hi hnu hKc hPK rho hsw hdelta hT hcmp hrho hin' c s htr hrec)

/-! ## The inverse input from VII.2.5 -/

/-- **The inverse input from the VII.2.5 target.** At the source normalization of
`SynthesisInverse.SynthesisInverseStatement` (one compact `K` serving as Iwasawa compact,
source compact and synthesis compact, the ambient Haar measure
`RationalDynamicSource.ambientHaar K hKc` of mass one on `K`, and the presentations of `C`),
that target and its premises give `RationalSemistandardDegreeZeroInverseInput` for the operator
built with the same data. -/
theorem rationalSemistandardDegreeZeroInverseInput_of_synthesisInverse
    (Q0 : ∀ t : Θ, OrbitPacketData (C.presentation t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2))
    (hmem0 : GlobalSynthesis.SchwartzMembershipStatement hG a ha muM d C.presentation hindex Q0
      K hKc hKc hPK rho)
    (hspecial0 : BruhatTits.SpecialCompact.SpecialCompactProperties F i nu
      (K : Subgroup (rationalPoints G)))
    (hd0 : ∀ t, (d t).compact = K) (hQ0 : ∀ t, (Q0 t).compact = K)
    (hsw0 : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hKc)
      (rationalXi hKc hPK) (rationalHeight (F := F) rho))
    (hcompact : Plancherel.WaldspurgerSourceNormalization.IsSourceCompactAt i K.toSubgroup)
    (hhaar : ∀ p, WavePacketPairing.SourceLeviQuotientHaar a muM (K := K) p)
    (hn : GlobalForm.DensityNonnegative hG a ha muM C.presentation Q0)
    (hdense : GlobalForm.DensityPositiveDense hG a ha muM C.presentation Q0)
    (h : SynthesisInverse.SynthesisInverseStatement hG a ha muM d hindex C Q0 hKc hPK rho) :
    letI := SynthesisInverse.sourceHaar_isMulRightInvariant hG hKc
    RationalSemistandardDegreeZeroInverseInput a ha muM d hG C hi hnu hKc hPK rho hsw0 hdelta hT
      C.presentation hindex Q0 K hKc hfiber hmem0 hspecial0 hd0 hQ0 :=
  fun psi => SynthesisInverse.fourier_synthesis hG a ha muM d hindex C Q0 hKc hPK rho hi hfiber hnu
    hspecial0 hd0 hQ0 hmem0 hsw0 hdelta hT hcompact hhaar hn hdense h psi

end Langlands.HarishChandraSchwartz
