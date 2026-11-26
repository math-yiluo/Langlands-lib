import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSynthesisSurjectivity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSynthesisInverse
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSynthesisIsometry
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierCovariance

/-! # Waldspurger VIII.1: surjectivity of `κ` versus (1) and (2), under VII.2.5

Waldspurger (2003), VIII.1, printed p. 320: by Théorème VII.2.5, Théorème VIII.1.1
is equivalent to (1) and (2) together. This module proves that equivalence and its
consequences from the VII.2.5 targets `SynthesisInverse.SynthesisInverseStatement`
and `SynthesisIsometry.SynthesisIsometryStatement`, taken as hypotheses with their
premises; the Weyl invariance part of membership comes from the VII.1.4 target
`RationalSemistandardFourierCovarianceStatement`, also a hypothesis. Under VIII.1.1
it constructs the complex-linear equivalence `κ : C^∞(Θ)_inv ≃ C(G)`, whose inverse is
`f ↦ psi_f`. It proves neither VII.1.4, VII.2.5 nor VIII.1.1. -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel.WaldspurgerSourceNormalization (IsSourceCompactAt)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion

open GlobalSynthesis GlobalForm

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

local instance equivalenceCompactOpen {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] :
    Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance equivalenceParabolicLC {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

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
  [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (C.presentation theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  {nu : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  [(RationalDynamicSource.ambientHaar K hK).IsMulRightInvariant]
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
  (hd : ∀ t, (d t).compact = K)
  (hQ : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu, (Q theta).compact = K)
  (hmem : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)
  (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
    (rationalXi hK hPK) (rationalHeight (F := F) rho))
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
    HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)
  (hcompact : IsSourceCompactAt i K.toSubgroup)
  (hhaar : ∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p)
  (hn : DensityNonnegative hG a ha mu C.presentation Q)
  (hdense : DensityPositiveDense hG a ha mu C.presentation Q)
  (hinv : SynthesisInverse.SynthesisInverseStatement hG a ha mu d hindex C Q hK hPK rho)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Invariant" => rationalSemistandardThetaInvariantSections C
set_option hygiene false in
set_option quotPrecheck false in
local notation "κ" => invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi
  semistandardSpectralFiberFiniteness hK hPK rho hmem hnu hspecial hd hQ
set_option hygiene false in
set_option quotPrecheck false in
local notation "fam" =>
  rationalSemistandardFourierFamily hG hi hnu hK hPK rho hsw a ha mu d hdelta hT

include hcompact hhaar hn hdense hinv in
/-- The second assertion of VII.2.5 at the displayed inputs: `psi_(κ ψ) = ψ` in the
full dependent product. -/
theorem fourierFamily_invariantSynthesis (psi : Invariant) : fam (κ psi) = psi.val.val :=
  SynthesisInverse.fourier_synthesis hG a ha mu d hindex C Q hK hPK rho hi
    semistandardSpectralFiberFiniteness hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn
    hdense hinv psi

include hcompact hhaar hn hdense hinv in
/-- The Fourier family of `κ ψ` lies in `C^∞(Θ)_inv`. -/
theorem fourierInvariantMembership_invariantSynthesis (psi : Invariant) :
    FourierInvariantMembership hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C (κ psi) := by
  have h := fourierFamily_invariantSynthesis hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd
    hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv psi
  exact ⟨h ▸ psi.val.property, h ▸ psi.property⟩

include hcompact hhaar hn hdense hinv in
/-- The invariant Fourier lift of `κ ψ` is `ψ`. -/
theorem fourierInvariantLift_invariantSynthesis (psi : Invariant)
    (hf : FourierInvariantMembership hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C (κ psi)) :
    fourierInvariantLift hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C (κ psi) hf = psi :=
  Subtype.ext (Subtype.ext (fourierFamily_invariantSynthesis hG a ha mu d hindex C Q hK hPK rho hi
    hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv psi))

include hcompact hhaar hn hdense hinv in
/-- Under VII.2.5, VIII.1.1 gives (1) and (2): each `f = κ ψ` has Fourier family `ψ`. -/
theorem fourierInversion_of_synthesisSurjectivity
    (hsurj : SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem
      hspecial hd hQ) :
    FourierInversionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K hK hmem
      hspecial hd hQ := by
  intro f
  obtain ⟨psi, rfl⟩ := hsurj f
  refine ⟨fourierInvariantMembership_invariantSynthesis hG a ha mu d hindex C Q hK hPK rho hi hnu
    hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv psi, ?_⟩
  rw [fourierInvariantLift_invariantSynthesis hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd
    hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv psi]

include hcompact hhaar hn hdense hinv in
/-- **VIII.1, printed p. 320.** Under VII.2.5, Théorème VIII.1.1 is equivalent to (1)
and (2) together, for the actual `κ` and the actual Fourier family. -/
theorem synthesisSurjectivity_iff_fourierInversion :
    SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem hspecial
        hd hQ ↔
      FourierInversionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K hK hmem
        hspecial hd hQ :=
  ⟨fourierInversion_of_synthesisSurjectivity hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd
      hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv,
    synthesisSurjectivity_of_fourierInversion hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem
      hspecial hd hQ hsw hdelta hT⟩

include hcompact hhaar hn hdense hinv in
/-- The same equivalence with the separate support and reconstruction targets. -/
theorem synthesisSurjectivity_iff_lift_and_reconstruction :
    SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem hspecial
        hd hQ ↔
      FourierInvariantLiftStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C ∧
        SynthesisReconstructionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K
          hK hmem hspecial hd hQ :=
  (synthesisSurjectivity_iff_fourierInversion hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd
    hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv).trans
    (fourierInversionStatement_iff hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K hK
      hmem hspecial hd hQ)

include hcompact hhaar hn hdense hinv in
/-- Under VII.2.5, injectivity of `f ↦ psi_f` gives reconstruction: `κ(psi_f)` and `f`
have the same Fourier family. -/
theorem synthesisReconstruction_of_fourierInjectivity
    (hinj : FourierInjectivityStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT) :
    SynthesisReconstructionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K hK
      hmem hspecial hd hQ := by
  intro f hf
  let psi := fourierInvariantLift hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C f hf
  have h := fourierFamily_invariantSynthesis hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd
    hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv psi
  have hz : fam (κ psi - f) = 0 := by
    rw [map_sub, h]
    exact sub_self _
  exact sub_eq_zero.mp (hinj _ hz)

include hcompact hhaar hn hdense hinv in
/-- Under VII.2.5, VIII.1.1 gives injectivity of `f ↦ psi_f`. -/
theorem fourierInjectivity_of_synthesisSurjectivity
    (hsurj : SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem
      hspecial hd hQ) :
    FourierInjectivityStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT := by
  intro f hf
  obtain ⟨psi, rfl⟩ := hsurj f
  have h := fourierFamily_invariantSynthesis hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd
    hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv psi
  have hpsi : psi = 0 := Subtype.ext (Subtype.ext (h.symm.trans hf))
  rw [hpsi, map_zero]

include hcompact hhaar hn hdense hinv in
/-- Under VII.2.5, VIII.1.1 is equivalent to invariant-carrier membership of every
`psi_f` together with injectivity of `f ↦ psi_f`. Finite support alone is not among
the conditions: membership also contains smoothness and Weyl invariance, and
injectivity is a separate condition. -/
theorem synthesisSurjectivity_iff_lift_and_injectivity :
    SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem hspecial
        hd hQ ↔
      FourierInvariantLiftStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C ∧
        FourierInjectivityStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT := by
  constructor
  · intro hsurj
    exact ⟨((synthesisSurjectivity_iff_lift_and_reconstruction hG a ha mu d hindex C Q hK hPK rho hi
      hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv).mp hsurj).1,
      fourierInjectivity_of_synthesisSurjectivity hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial
        hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv hsurj⟩
  · rintro ⟨hlift, hinj⟩
    exact (synthesisSurjectivity_iff_lift_and_reconstruction hG a ha mu d hindex C Q hK hPK rho hi
      hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv).mpr
      ⟨hlift, synthesisReconstruction_of_fourierInjectivity hG a ha mu d hindex C Q hK hPK rho hi hnu
        hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv hinj⟩

include hcompact hhaar hn hdense hinv in
/-- Under VII.2.5, VIII.1.1 gives the unquotiented formula (2): every Schwartz `f` is, at
every point, the weighted sum of the actual wave packets of the components of its own
Fourier family. -/
theorem unquotientedReconstruction_of_synthesisSurjectivity
    (hsurj : SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem
      hspecial hd hQ) :
    UnquotientedReconstructionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C.presentation
      hindex Q K hK := by
  have h := (fourierInversionStatement_iff hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K
    hK hmem hspecial hd hQ).mp (fourierInversion_of_synthesisSurjectivity hG a ha mu d hindex C Q hK
      hPK rho hi hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv hsurj)
  exact (synthesisReconstruction_iff_unquotiented hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C
    hindex Q K hK hmem hspecial hd hQ fun f => (h.1 f).2).mp h.2

/-! ## The covariance part of membership, from VII.1.4 -/

section Covariance

variable (hcov : RationalSemistandardFourierCovarianceStatement hi hnu hK hPK rho hsw a ha mu d hdelta
  hT C)

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
include hd hhaar hcov in
/-- The VII.1.4 target gives the pointwise Weyl invariance of every `psi_f`: its I.1
normalization premise follows from the source quotient Haar normalization on the common
compact. -/
theorem isWeylInvariant_fourierFamily_of_covariance (f : RationalSchwartzSpace hK hPK rho) :
    IsWeylInvariant C (fam f) := by
  have hquot : SourceMeasure.IntrinsicQuotientNormalization a mu d := by
    intro p
    rw [hd p]
    exact hhaar p
  exact (rationalSemistandardFourierCovarianceStatement_iff hi hnu hK hPK rho hsw a ha mu d hdelta
    hT C).mp hcov hquot f

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
include hd hhaar hcov in
/-- Under VII.1.4, invariant-carrier membership of every `psi_f` is exactly its
membership in the coherent smooth finite-support carrier. -/
theorem fourierInvariantLiftStatement_iff_smoothSections_of_covariance :
    FourierInvariantLiftStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C ↔
      ∀ f : RationalSchwartzSpace hK hPK rho,
        fam f ∈ rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d :=
  ⟨fun h f => (h f).1, fun h f => ⟨h f, isWeylInvariant_fourierFamily_of_covariance hG a ha mu d C
    hK hPK rho hi hnu hd hsw hdelta hT hhaar hcov f⟩⟩

include hcompact hhaar hn hdense hinv hcov in
/-- Under VII.2.5 and VII.1.4, VIII.1.1 is equivalent to coherent smoothness with finite
support of every `psi_f` together with the synthesis reconstruction `κ(psi_f) = f`. -/
theorem synthesisSurjectivity_iff_smoothSections_and_reconstruction :
    SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem hspecial
        hd hQ ↔
      (∀ f : RationalSchwartzSpace hK hPK rho,
          fam f ∈ rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) ∧
        SynthesisReconstructionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K
          hK hmem hspecial hd hQ := by
  rw [synthesisSurjectivity_iff_lift_and_reconstruction hG a ha mu d hindex C Q hK hPK rho hi hnu
    hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv,
    fourierInvariantLiftStatement_iff_smoothSections_of_covariance hG a ha mu d C hK hPK rho hi hnu
      hd hsw hdelta hT hhaar hcov]

include hcompact hhaar hn hdense hinv hcov in
/-- Under VII.2.5 and VII.1.4, VIII.1.1 is equivalent to coherent smoothness with finite
support of every `psi_f` together with injectivity of `f ↦ psi_f`. -/
theorem synthesisSurjectivity_iff_smoothSections_and_injectivity :
    SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem hspecial
        hd hQ ↔
      (∀ f : RationalSchwartzSpace hK hPK rho,
          fam f ∈ rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) ∧
        FourierInjectivityStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT := by
  rw [synthesisSurjectivity_iff_lift_and_injectivity hG a ha mu d hindex C Q hK hPK rho hi hnu
    hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv,
    fourierInvariantLiftStatement_iff_smoothSections_of_covariance hG a ha mu d C hK hPK rho hi hnu
      hd hsw hdelta hT hhaar hcov]

include hcompact hhaar hn hdense hinv hcov in
/-- **VIII.1, printed p. 320, in the source form.** Under VII.2.5, VII.1.4 and componentwise
smoothness of every `psi_f` (the conclusion of VII.1.3), Théorème VIII.1.1 is equivalent to
(1), finite support of every `psi_f`, together with (2), the unquotiented formula
`f = Σ_(O,P) c(G|M)^-2 γ(G|M)^-1 |W^M| |W^G|^-1 |P(M)|^-1 f_(psi_f[O,P])`. -/
theorem synthesisSurjectivity_iff_finiteSupport_and_unquotiented
    (hsm : ∀ (f : RationalSchwartzSpace hK hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha mu),
      fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) :
    SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem hspecial
        hd hQ ↔
      RationalSemistandardFourierFiniteSupportStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta
          hT ∧
        UnquotientedReconstructionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT
          C.presentation hindex Q K hK := by
  constructor
  · intro hsurj
    have h := (fourierInversionStatement_iff hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex
      Q K hK hmem hspecial hd hQ).mp (fourierInversion_of_synthesisSurjectivity hG a ha mu d hindex
        C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv hsurj)
    exact ⟨fun f => (h.1 f).1.2, unquotientedReconstruction_of_synthesisSurjectivity hG a ha mu d
      hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv
      hsurj⟩
  · rintro ⟨hfs, hU⟩
    exact (synthesisSurjectivity_iff_smoothSections_and_reconstruction hG a ha mu d hindex C Q hK
      hPK rho hi hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv hcov).mpr
      ⟨fun f => ⟨hsm f, hfs f⟩, synthesisReconstruction_of_unquotiented hG hi hnu hK hPK rho hsw a
        ha mu d hdelta hT C hindex Q K hK hmem hspecial hd hQ hU⟩

end Covariance

/-! ## The linear equivalence -/

section Equivalence

variable (hsurj : SynthesisSurjectivityStatement hG hi hnu hK hPK rho a ha mu d C hindex Q K hK hmem
  hspecial hd hQ)

include hcompact hhaar hn hdense hinv in
/-- Under VII.2.5 and VIII.1.1, `κ` is a complex-linear bijection from `C^∞(Θ)_inv` onto
the Harish-Chandra Schwartz space. Injectivity is the VII.2.5 consequence
`SynthesisInverse.invariantSynthesis_injective`. -/
def synthesisLinearEquiv : Invariant ≃ₗ[ℂ] RationalSchwartzSpace hK hPK rho :=
  LinearEquiv.ofBijective κ
    ⟨SynthesisInverse.invariantSynthesis_injective hG a ha mu d hindex C Q hK hPK rho hi
      semistandardSpectralFiberFiniteness hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn
      hdense hinv, hsurj⟩

omit [(RationalDynamicSource.ambientHaar K hK).IsMulRightInvariant] in
theorem synthesisLinearEquiv_apply (psi : Invariant) :
    synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw hdelta
        hT hcompact hhaar hn hdense hinv hsurj psi = κ psi :=
  rfl

omit [(RationalDynamicSource.ambientHaar K hK).IsMulRightInvariant] in
/-- Pointwise formula of the equivalence: the unquotiented weighted source sum of VI.3. -/
theorem synthesisLinearEquiv_apply_apply (psi : Invariant) (g : rationalPoints G) :
    synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw hdelta
        hT hcompact hhaar hn hdense hinv hsurj psi g =
      ∑ theta ∈ psi.val.property.2.toFinset,
        (sourceWeight hG C.presentation K hK theta.1 : ℂ) *
          componentPacket hG a ha mu d C.presentation hindex Q theta
            (rationalSemistandardThetaComponent a ha mu d theta psi.val) g :=
  weightedSynthesis_apply hG a ha mu d C.presentation hindex Q K hK psi.val g

/-- The inverse of the equivalence is the actual Fourier family: the underlying family
of `e.symm f` is `psi_f`. -/
theorem synthesisLinearEquiv_symm_val (f : RationalSchwartzSpace hK hPK rho) :
    ((synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw hdelta
        hT hcompact hhaar hn hdense hinv hsurj).symm f).val.val = fam f := by
  set e := synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw
    hdelta hT hcompact hhaar hn hdense hinv hsurj
  have h := fourierFamily_invariantSynthesis hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd
    hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv (e.symm f)
  have hf : κ (e.symm f) = f := e.apply_symm_apply f
  rw [hf] at h
  exact h.symm

/-- The inverse of the equivalence is the invariant Fourier lift. -/
theorem synthesisLinearEquiv_symm_eq_fourierInvariantLift (f : RationalSchwartzSpace hK hPK rho)
    (hf : FourierInvariantMembership hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C f) :
    (synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw hdelta
        hT hcompact hhaar hn hdense hinv hsurj).symm f =
      fourierInvariantLift hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C f hf :=
  Subtype.ext (Subtype.ext (synthesisLinearEquiv_symm_val hG a ha mu d hindex C Q hK hPK rho hi hnu
    hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense hinv hsurj f))

omit [(RationalDynamicSource.ambientHaar K hK).IsMulRightInvariant] in
/-- Under the VII.2.5 isometry target, the equivalence carries the source integral
Hermitian form to the integral pairing on `G` for the source Haar measure: for all
Schwartz `f'` and `f`, `∫_G conj(f') f dg = B(psi_f', psi_f)`. -/
theorem pairing_eq_invariantGlobalForm_symm
    (hiso : SynthesisIsometry.SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho)
    (f' f : RationalSchwartzSpace hK hPK rho) :
    HarishChandraSchwartz.pairing (RationalDynamicSource.ambientHaar K hK) f' f =
      invariantGlobalForm hG a ha mu d C.presentation hindex Q K hK C
        ((synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw
          hdelta hT hcompact hhaar hn hdense hinv hsurj).symm f')
        ((synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw
          hdelta hT hcompact hhaar hn hdense hinv hsurj).symm f) := by
  set e := synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw
    hdelta hT hcompact hhaar hn hdense hinv hsurj
  have h := SynthesisIsometry.pairing_synthesis_eq_form hG a ha mu d hindex C Q hK hPK rho hi
    semistandardSpectralFiberFiniteness hnu hspecial hd hQ hmem hcompact hhaar hsw hn hiso
    (e.symm f') (e.symm f)
  have h' : κ (e.symm f') = f' := e.apply_symm_apply f'
  have h'' : κ (e.symm f) = f := e.apply_symm_apply f
  have hc : ∀ {x y : RationalSchwartzSpace hK hPK rho}, x = y →
      (x : rationalPoints G → ℂ) = (y : rationalPoints G → ℂ) := fun hxy => congrArg _ hxy
  exact (congrArg₂ (HarishChandraSchwartz.pairing (RationalDynamicSource.ambientHaar K hK))
    (hc h') (hc h'')).symm.trans h

omit [(RationalDynamicSource.ambientHaar K hK).IsMulRightInvariant] in
/-- The same identity in `L²(G)`, through the existing inclusion `Space.toL2` of the
Schwartz space defined by the weight condition. -/
theorem inner_toL2_eq_invariantGlobalForm_symm
    (hiso : SynthesisIsometry.SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho)
    (f' f : RationalSchwartzSpace hK hPK rho) :
    inner ℂ (Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) f')
        (Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) f) =
      invariantGlobalForm hG a ha mu d C.presentation hindex Q K hK C
        ((synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw
          hdelta hT hcompact hhaar hn hdense hinv hsurj).symm f')
        ((synthesisLinearEquiv hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ hmem hsw
          hdelta hT hcompact hhaar hn hdense hinv hsurj).symm f) :=
  (Space.inner_toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) f' f).trans
    (pairing_eq_invariantGlobalForm_symm hG a ha mu d hindex C Q hK hPK rho hi hnu hspecial hd hQ
      hmem hsw hdelta hT hcompact hhaar hn hdense hinv hsurj hiso f' f)

end Equivalence

end Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion
