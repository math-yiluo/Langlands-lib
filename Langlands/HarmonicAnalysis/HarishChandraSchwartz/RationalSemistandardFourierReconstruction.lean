import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariantSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierThetaSupport
import Langlands.GroupScheme.Rational.SemistandardSpectralFiberFinitenessProof
import Langlands.GroupScheme.Rational.SemistandardProperLeviRankProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardComparisonHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacketFourier

/-! # Waldspurger VIII.1 (1) and (2): Fourier support and synthesis reconstruction

Waldspurger (2003), VIII.1, printed p. 320. The targets of this module are
Prop-valued definitions; the module proves only their elementary relations. -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel.WaldspurgerSourceNormalization (IsSourceCompactAt)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion

open GlobalSynthesis

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

local instance reconstructionCompactOpen {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] :
    Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance reconstructionParabolicLC {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

section FixedData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {nu : cocharacterLattice S} (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
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
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
set_option quotPrecheck false in
local notation "fam" =>
  rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT
set_option hygiene false in
set_option quotPrecheck false in
local notation "SmoothFamilies" => rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d

/-! ## The zero case of formula (2) -/

/-- The zero case of VIII.1 (2): a Schwartz function whose actual Fourier family
vanishes is zero. It involves the Fourier data only. -/
def FourierInjectivityStatement : Prop :=
  ∀ f : RationalSchwartzSpace hKc hPK rho, fam f = 0 → f = 0

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
theorem fourierInjectivityStatement_iff :
    FourierInjectivityStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT ↔
      Function.Injective fam :=
  (injective_iff_map_eq_zero _).symm

/-! ## Formula (2) without the Weyl quotient -/

section Unquotiented

variable (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (rs theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))

/-- The right side of VIII.1 (2) at `g`, before the Weyl quotient: the sum over the
finite literal support of `psi_f` of
`c(G|M)^-2 gamma(G|M)^-1 |W^M| |W^G|^-1 |P(M)|^-1 f_(psi_f[O,P])(g)`, with the actual
source packets and unquotiented source coefficients. Componentwise smoothness `hsm`
types each packet; finiteness `hfs` of the support controls the sum. -/
def unquotientedReconstructionSum (f : RationalSchwartzSpace hKc hPK rho)
    (hsm : ∀ t : Θ, fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (fam f)).Finite)
    (g : rationalPoints G) : ℂ :=
  ∑ t ∈ hfs.toFinset, (sourceWeight hG rs K0 hK0 t.1 : ℂ) *
    componentPacket hG a ha mu d rs hindex Q t ⟨fam f t, hsm t⟩ g

/-- The actual smooth finite-support family with the components of `psi_f`. -/
def fourierSmoothLift (f : RationalSchwartzSpace hKc hPK rho)
    (hsm : ∀ t : Θ, fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (fam f)).Finite) :
    SmoothFamilies :=
  ⟨fam f, hsm, hfs⟩

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
@[simp] theorem fourierSmoothLift_val (f : RationalSchwartzSpace hKc hPK rho)
    (hsm : ∀ t : Θ, fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (fam f)).Finite) :
    (fourierSmoothLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT f hsm hfs).val = fam f :=
  rfl

/-- The unquotiented sum is the actual weighted synthesis of the smooth lift of `psi_f`. -/
theorem unquotientedReconstructionSum_eq_weightedSynthesis
    (f : RationalSchwartzSpace hKc hPK rho)
    (hsm : ∀ t : Θ, fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (fam f)).Finite)
    (g : rationalPoints G) :
    unquotientedReconstructionSum hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT rs hindex Q K0 hK0
        f hsm hfs g =
      weightedSynthesis hG a ha mu d rs hindex Q K0 hK0
        (fourierSmoothLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT f hsm hfs) g := by
  rw [weightedSynthesis_apply]
  rfl

/-- The unquotiented formula (2) at one Schwartz function: whenever `psi_f` has smooth
components and finite support, `f` is the weighted sum of the wave packets of its
own Fourier components. The support premise is a visible hypothesis. -/
def UnquotientedReconstructionAt (f : RationalSchwartzSpace hKc hPK rho) : Prop :=
  ∀ (hsm : ∀ t : Θ, fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (fam f)).Finite)
    (g : rationalPoints G),
    f g = unquotientedReconstructionSum hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT rs hindex Q
      K0 hK0 f hsm hfs g

/-- Waldspurger VIII.1 (2) without the Weyl quotient, for every Schwartz function
whose Fourier family has smooth components and finite support. -/
def UnquotientedReconstructionStatement : Prop :=
  ∀ f : RationalSchwartzSpace hKc hPK rho,
    UnquotientedReconstructionAt hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT rs hindex Q K0 hK0 f

/-- The pointwise formula is the equality of `f` with the weighted synthesis of the
smooth lift of `psi_f`, for any smoothness and support witnesses. -/
theorem unquotientedReconstructionAt_iff (f : RationalSchwartzSpace hKc hPK rho) :
    UnquotientedReconstructionAt hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT rs hindex Q K0 hK0 f ↔
      ∀ (hsm : ∀ t : Θ, fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
        (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (fam f)).Finite),
        weightedSynthesis hG a ha mu d rs hindex Q K0 hK0
          (fourierSmoothLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT f hsm hfs) = ⇑f := by
  constructor
  · intro h hsm hfs
    funext g
    rw [← unquotientedReconstructionSum_eq_weightedSynthesis]
    exact (h hsm hfs g).symm
  · intro h hsm hfs g
    rw [unquotientedReconstructionSum_eq_weightedSynthesis]
    exact (congrFun (h hsm hfs) g).symm

/-- A Schwartz function with vanishing Fourier family is zero under the unquotiented
formula. This is the use of VIII.1 (2) for a Levi subgroup in the proof of VIII.2.1. -/
theorem eq_zero_of_fourierFamily_eq_zero
    (h : UnquotientedReconstructionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT rs
      hindex Q K0 hK0)
    (f : RationalSchwartzSpace hKc hPK rho) (hf : fam f = 0) : f = 0 := by
  have hsm : ∀ t : Θ, fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t := by
    intro t
    rw [hf]
    exact Submodule.zero_mem _
  have hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (fam f)).Finite := by
    rw [hf, rationalSemistandardThetaSupport_zero]
    exact Set.finite_empty
  have hlift : fourierSmoothLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT f hsm hfs = 0 :=
    Subtype.ext hf
  have h0 := (unquotientedReconstructionAt_iff hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT rs
    hindex Q K0 hK0 f).mp (h f) hsm hfs
  rw [hlift, map_zero] at h0
  ext g
  exact (congrFun h0 g).symm

/-- The unquotiented formula (2) contains its zero case. -/
theorem fourierInjectivity_of_unquotientedReconstruction
    (h : UnquotientedReconstructionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT rs
      hindex Q K0 hK0) :
    FourierInjectivityStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT := fun f hf =>
  eq_zero_of_fourierFamily_eq_zero hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT rs hindex Q K0 hK0
    h f hf

end Unquotiented

/-! ## The invariant lift and the actual synthesis `κ` -/

section Invariant

variable (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (C.presentation theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))
  (hsynth : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K0 hK0 hKc hPK rho)
  (hspecial : SpecialCompactProperties F i nu (K0 : Subgroup (rationalPoints G)))
  (hd : ∀ t, (d t).compact = K0) (hQ : ∀ theta : Θ, (Q theta).compact = K0)

set_option hygiene false in
set_option quotPrecheck false in
local notation "κ" => invariantSynthesis hG a ha mu d C.presentation hindex Q K0 hK0 C hi
  semistandardSpectralFiberFiniteness hKc hPK rho hsynth hnu hspecial hd hQ

/-- Membership of `psi_f` in Waldspurger's invariant spectral space `C^∞(Θ)_inv`:
coherent smooth components, finite literal support (VIII.1 (1)) and the pointwise
Weyl invariance of the carrier (the conclusion of VII.1.4). -/
def FourierInvariantMembership (f : RationalSchwartzSpace hKc hPK rho) : Prop :=
  fam f ∈ SmoothFamilies ∧ IsWeylInvariant C (fam f)

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
theorem fourierInvariantMembership_iff (f : RationalSchwartzSpace hKc hPK rho) :
    FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f ↔
      (∀ t : Θ, fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) ∧
        (rationalSemistandardThetaSupport.{u, uV} a ha mu (fam f)).Finite ∧
          IsWeylInvariant C (fam f) :=
  and_assoc

/-- The actual Fourier family of `f` as an element of `C^∞(Θ)_inv`, from a membership
witness. No preimage is selected: the underlying family is `psi_f` itself. -/
def fourierInvariantLift (f : RationalSchwartzSpace hKc hPK rho)
    (hf : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f) :
    rationalSemistandardThetaInvariantSections C :=
  ⟨⟨fam f, hf.1⟩, hf.2⟩

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
@[simp] theorem fourierInvariantLift_val (f : RationalSchwartzSpace hKc hPK rho)
    (hf : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f) :
    (fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f hf).val.val = fam f :=
  rfl

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- The lift does not depend on the membership witness. -/
theorem fourierInvariantLift_congr (f : RationalSchwartzSpace hKc hPK rho)
    (hf hf' : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f) :
    fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f hf =
      fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f hf' :=
  rfl

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- The lift is that of any two Schwartz functions with the same Fourier family. -/
theorem fourierInvariantLift_eq_of_fourierFamily_eq {f f' : RationalSchwartzSpace hKc hPK rho}
    (hf : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f)
    (hf' : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f')
    (h : fam f = fam f') :
    fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f hf =
      fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f' hf' :=
  Subtype.ext (Subtype.ext h)

/-- VIII.1 (1) with VII.1.3 and VII.1.4: the Fourier family of every Schwartz
function lies in `C^∞(Θ)_inv`. -/
def FourierInvariantLiftStatement : Prop :=
  ∀ f : RationalSchwartzSpace hKc hPK rho,
    FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- Invariant-carrier membership of every `psi_f` is exactly componentwise
smoothness (VII.1.3), finite support (VIII.1 (1), the Library's
`RationalSemistandardFourierFiniteSupportStatement`) and pointwise Weyl invariance
(the conclusion of VII.1.4), each for every Schwartz function. -/
theorem fourierInvariantLiftStatement_iff :
    FourierInvariantLiftStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C ↔
      (∀ (f : RationalSchwartzSpace hKc hPK rho) (t : Θ),
          fam f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) ∧
        RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
          a ha mu d hdelta hT ∧
        ∀ f : RationalSchwartzSpace hKc hPK rho, IsWeylInvariant C (fam f) :=
  ⟨fun h => ⟨fun f => (h f).1.1, fun f => (h f).1.2, fun f => (h f).2⟩,
    fun h f => ⟨⟨h.1 f, h.2.1 f⟩, h.2.2 f⟩⟩

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
/-- Invariant-carrier membership from the published VII.1.3 smoothness target and its
analytic inputs at every component, the VIII.1 (1) support target and the pointwise
Weyl invariance concluded by VII.1.4. -/
theorem fourierInvariantLiftStatement_of_smoothness
    (hS : RationalSemistandardFourierFamilySmoothnessStatement (muG := muG) hG hi hnu hKc hPK rho
      hsw a ha mu d hdelta hT)
    (hin : ∀ t : Θ, ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1))
      (XiM sigmaM : levi t.1 → ℝ),
        RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
          t.1 (chosenLeviModel t.1) (d t.1)
          (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
          muL muU XiM sigmaM)
    (hfs : RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha mu d hdelta hT)
    (hcov : ∀ f : RationalSchwartzSpace hKc hPK rho, IsWeylInvariant C (fam f)) :
    FourierInvariantLiftStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C :=
  (fourierInvariantLiftStatement_iff hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C).mpr
    ⟨rationalSemistandardFourierFamily_mem_componentSpace_of_smoothness hG hi hnu hKc hPK rho
      hsw a ha mu d hdelta hT hS hin, hfs, hcov⟩

/-- Under a membership witness, `κ` of the lift of `psi_f` is the unquotiented sum of
VIII.1 (2) at every point. -/
theorem invariantSynthesis_fourierInvariantLift_apply (f : RationalSchwartzSpace hKc hPK rho)
    (hf : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f)
    (g : rationalPoints G) :
    κ (fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f hf) g =
      unquotientedReconstructionSum hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C.presentation
        hindex Q K0 hK0 f hf.1.1 hf.1.2 g :=
  (unquotientedReconstructionSum_eq_weightedSynthesis hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT
    C.presentation hindex Q K0 hK0 f hf.1.1 hf.1.2 g).symm

/-- The actual synthesis reconstruction at one Schwartz function: for every witness
that `psi_f` lies in `C^∞(Θ)_inv`, `κ(psi_f) = f`. -/
def SynthesisReconstructionAt (f : RationalSchwartzSpace hKc hPK rho) : Prop :=
  ∀ hf : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f,
    κ (fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f hf) = f

/-- VIII.1 (2) for the actual `κ`: reconstruction of every Schwartz function whose
Fourier family lies in `C^∞(Θ)_inv`. The membership is a visible premise. -/
def SynthesisReconstructionStatement : Prop :=
  ∀ f : RationalSchwartzSpace hKc hPK rho,
    SynthesisReconstructionAt hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0 hK0
      hsynth hspecial hd hQ f

/-- Under a membership witness, `κ(psi_f) = f` is exactly the unquotiented formula
of VIII.1 (2) at `f`, for that witness. -/
theorem invariantSynthesis_fourierInvariantLift_eq_iff (f : RationalSchwartzSpace hKc hPK rho)
    (hf : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f) :
    κ (fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f hf) = f ↔
      ∀ g : rationalPoints G,
        f g = unquotientedReconstructionSum hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT
          C.presentation hindex Q K0 hK0 f hf.1.1 hf.1.2 g := by
  constructor
  · intro h g
    rw [← invariantSynthesis_fourierInvariantLift_apply hG hi hnu hKc hPK rho hsw a ha mu d hdelta
      hT C hindex Q K0 hK0 hsynth hspecial hd hQ f hf g, h]
  · intro h
    ext g
    rw [invariantSynthesis_fourierInvariantLift_apply hG hi hnu hKc hPK rho hsw a ha mu d hdelta
      hT C hindex Q K0 hK0 hsynth hspecial hd hQ f hf g]
    exact (h g).symm

/-- The unquotiented formula implies the reconstruction by the actual `κ`. -/
theorem synthesisReconstructionAt_of_unquotiented (f : RationalSchwartzSpace hKc hPK rho)
    (h : UnquotientedReconstructionAt hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C.presentation
      hindex Q K0 hK0 f) :
    SynthesisReconstructionAt hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0 hK0
      hsynth hspecial hd hQ f := fun hf =>
  (invariantSynthesis_fourierInvariantLift_eq_iff hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C
    hindex Q K0 hK0 hsynth hspecial hd hQ f hf).mpr (h hf.1.1 hf.1.2)

/-- Conversely, when `psi_f` is Weyl invariant (the conclusion of VII.1.4 at `f`), the
reconstruction by `κ` gives the unquotiented formula at `f`. -/
theorem unquotientedReconstructionAt_of_synthesisReconstructionAt
    (f : RationalSchwartzSpace hKc hPK rho) (hcov : IsWeylInvariant C (fam f))
    (h : SynthesisReconstructionAt hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0 hK0
      hsynth hspecial hd hQ f) :
    UnquotientedReconstructionAt hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C.presentation
      hindex Q K0 hK0 f := fun hsm hfs =>
  (invariantSynthesis_fourierInvariantLift_eq_iff hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C
    hindex Q K0 hK0 hsynth hspecial hd hQ f ⟨⟨hsm, hfs⟩, hcov⟩).mp (h ⟨⟨hsm, hfs⟩, hcov⟩)

theorem synthesisReconstruction_of_unquotiented
    (h : UnquotientedReconstructionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT
      C.presentation hindex Q K0 hK0) :
    SynthesisReconstructionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0
      hK0 hsynth hspecial hd hQ := fun f =>
  synthesisReconstructionAt_of_unquotiented hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex
    Q K0 hK0 hsynth hspecial hd hQ f (h f)

/-- Given pointwise Weyl invariance of every `psi_f`, the two forms of VIII.1 (2)
are equivalent. -/
theorem synthesisReconstruction_iff_unquotiented
    (hcov : ∀ f : RationalSchwartzSpace hKc hPK rho, IsWeylInvariant C (fam f)) :
    SynthesisReconstructionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0
        hK0 hsynth hspecial hd hQ ↔
      UnquotientedReconstructionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT
        C.presentation hindex Q K0 hK0 :=
  ⟨fun h f => unquotientedReconstructionAt_of_synthesisReconstructionAt hG hi hnu hKc hPK rho hsw
      a ha mu d hdelta hT C hindex Q K0 hK0 hsynth hspecial hd hQ f (hcov f) (h f),
    synthesisReconstruction_of_unquotiented hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C
      hindex Q K0 hK0 hsynth hspecial hd hQ⟩

/-- VIII.1 (1) and (2) together: every Schwartz function has its actual
finite-support invariant Fourier lift, and `κ(psi_f) = f`. -/
def FourierInversionStatement : Prop :=
  ∀ f : RationalSchwartzSpace hKc hPK rho,
    ∃ hf : FourierInvariantMembership hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f,
      κ (fourierInvariantLift hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C f hf) = f

/-- The full target is the conjunction of the separate support and reconstruction
targets. -/
theorem fourierInversionStatement_iff :
    FourierInversionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0 hK0
        hsynth hspecial hd hQ ↔
      FourierInvariantLiftStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C ∧
        SynthesisReconstructionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q
          K0 hK0 hsynth hspecial hd hQ :=
  ⟨fun h => ⟨fun f => (h f).1, fun f _hf => (h f).2⟩,
    fun h f => ⟨h.1 f, h.2 f (h.1 f)⟩⟩

/-- The full target makes every Schwartz function a value of `κ` at its own
Fourier lift. -/
theorem surjective_of_fourierInversion
    (h : FourierInversionStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT C hindex Q K0
      hK0 hsynth hspecial hd hQ) :
    Function.Surjective κ := fun f =>
  ⟨_, (h f).2⟩

end Invariant

end FixedData

/-! ## Local targets for one group and their closures

The local targets fix the field and the group and quantify over every choice of the
remaining data. The Fourier-only targets (finite support and injectivity) allow every
Iwasawa compact, every matrix representation `rho` satisfying the weight condition, every
Haar measure on `G(F)` and every split-central quotient Haar measure; the source choices
are special cases. The reconstruction targets use the I.1 normalizations: one compact
`K` is the source special compact (`IsSourceCompactAt`), the compact of the
Harish-Chandra Schwartz space and of every compact picture and scalar datum; the height
comes from a closed matrix embedding `rho` with `K` in its integral subgroup; the Haar
measure of `G(F)` is `RationalDynamicSource.ambientHaar K hK`, of mass one on `K`; and
the split-central quotient Haar measures give the image of `K ∩ M` mass one. -/

/-- The source Haar measure of mass one on `K` is right invariant, by unimodularity. -/
theorem sourceAmbientHaar_isMulRightInvariant {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {K : OpenSubgroup (rationalPoints G)} (hK : IsCompact (K : Set (rationalPoints G))) :
    (RationalDynamicSource.ambientHaar K hK).IsMulRightInvariant :=
  Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one (ambient_modularCharacter hG)
    (RationalDynamicSource.ambientHaar K hK)

/-- Local VIII.1 (1) for one group: for all Fourier data, the actual Fourier family of
every Schwartz function has finite literal support. -/
def RationalLocalFourierFiniteSupportStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  ∀ (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
    (N : ℕ) [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure] [muG.IsMulRightInvariant]
    (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
    (T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F)))
    (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
    (ha : ∀ t, IsSplitComponent (a t))
    [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
    [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
    [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
    (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
    [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
    (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
    (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
    (hT : ∀ (p : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
        ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
      HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj
          A.obj).representation),
    RationalSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT

/-- Local zero case of VIII.1 (2) for one group: for all Fourier data, a Schwartz
function with vanishing actual Fourier family is zero. No synthesis datum, measure
normalization, support or orbit-finiteness conclusion for the group is a premise. -/
def RationalLocalFourierInjectivityStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  ∀ (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
    (N : ℕ) [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure] [muG.IsMulRightInvariant]
    (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
    (T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F)))
    (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
    (ha : ∀ t, IsSplitComponent (a t))
    [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
    [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
    [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
    (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
    [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
    (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
    (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
    (hT : ∀ (p : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
        ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
      HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj
          A.obj).representation),
    FourierInjectivityStatement hG hi hnu hKc hPK rho hsw a ha mu d hdelta hT

/-- Local VIII.1 (2) without the Weyl quotient, for one group: for all normalized source
data, every Schwartz function whose Fourier family has smooth components and finite
support is the weighted sum of the source packets of its Fourier components. No orbit
finiteness, support or Plancherel conclusion for the group is a premise. -/
def RationalLocalUnquotientedReconstructionStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  ∀ (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
    (N : ℕ) [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (_hrho : IsClosedSubgroup rho)
    (_hKrho : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) rho)
    (T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F)))
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
    (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
    (hT : ∀ (p : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
        ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
      HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj
          A.obj).representation)
    (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho))
    (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
    (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
    (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
      OrbitPacketData (rs theta.1)
        (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
          (mu theta.1) theta.2)),
    IsSourceCompactAt i K.toSubgroup →
    (∀ t, (d t).compact = K) →
    (∀ theta : RationalSemistandardTheta.{u, uV} a ha mu, (Q theta).compact = K) →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    haveI := sourceAmbientHaar_isMulRightInvariant hG hK
    UnquotientedReconstructionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT rs hindex Q
      K hK

/-- Local VIII.1 (2) for the actual `κ`, for one group: for all normalized source data,
`κ(psi_f) = f` whenever `psi_f` lies in `C^∞(Θ)_inv`. -/
def RationalLocalSynthesisReconstructionStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  ∀ (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
    (N : ℕ) [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (_hrho : IsClosedSubgroup rho)
    (_hKrho : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) rho)
    (T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F)))
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
    (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
    (hT : ∀ (p : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
        ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
      HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj
          A.obj).representation)
    (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho))
    (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
    (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
    (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
      OrbitPacketData (C.presentation theta.1)
        (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
          (mu theta.1) theta.2))
    (hsynth : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)
    (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K)
    (hQ : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu, (Q theta).compact = K),
    IsSourceCompactAt i K.toSubgroup →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    haveI := sourceAmbientHaar_isMulRightInvariant hG hK
    SynthesisReconstructionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K hK
      hsynth hspecial hd hQ

/-- Local VIII.1 (1) and (2) for the actual `κ`, for one group: for all normalized source
data, every `psi_f` lies in `C^∞(Θ)_inv` and `κ(psi_f) = f`. -/
def RationalLocalFourierInversionStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  ∀ (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
    (N : ℕ) [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (_hrho : IsClosedSubgroup rho)
    (_hKrho : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) rho)
    (T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F)))
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
    (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
    (hT : ∀ (p : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
        ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
      HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj
          A.obj).representation)
    (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho))
    (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
    (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
    (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
      OrbitPacketData (C.presentation theta.1)
        (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
          (mu theta.1) theta.2))
    (hsynth : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)
    (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K)
    (hQ : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu, (Q theta).compact = K),
    IsSourceCompactAt i K.toSubgroup →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    haveI := sourceAmbientHaar_isMulRightInvariant hG hK
    FourierInversionStatement hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K hK
      hsynth hspecial hd hQ

section LocalRelations

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The local unquotiented formula gives the local reconstruction by `κ`, with the
presentations of the comparison data. -/
theorem rationalLocalSynthesisReconstruction_of_unquotiented
    (h : RationalLocalUnquotientedReconstructionStatement.{u, uV} G) :
    RationalLocalSynthesisReconstructionStatement.{u, uV} G := by
  intro hG S i hi nu hnu K hK hPK N _ rho hrho hKrho T _ a ha _ _ _ _ mu _ _ d hdelta hT hsw C
    hindex Q hsynth hspecial hd hQ hsrc hn
  have := sourceAmbientHaar_isMulRightInvariant hG hK
  exact synthesisReconstruction_of_unquotiented hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C
    hindex Q K hK hsynth hspecial hd hQ
    (h hG S i hi nu hnu K hK hPK N rho hrho hKrho T a ha mu d hdelta hT hsw C.presentation hindex Q
      hsrc hd hQ hn)

/-- The local full target contains the local reconstruction target. -/
theorem rationalLocalSynthesisReconstruction_of_fourierInversion
    (h : RationalLocalFourierInversionStatement.{u, uV} G) :
    RationalLocalSynthesisReconstructionStatement.{u, uV} G := by
  intro hG S i hi nu hnu K hK hPK N _ rho hrho hKrho T _ a ha _ _ _ _ mu _ _ d hdelta hT hsw C
    hindex Q hsynth hspecial hd hQ hsrc hn
  have := sourceAmbientHaar_isMulRightInvariant hG hK
  exact ((fourierInversionStatement_iff hG hi hnu hK hPK rho hsw a ha mu d hdelta hT C hindex Q K
    hK hsynth hspecial hd hQ).mp
    (h hG S i hi nu hnu K hK hPK N rho hrho hKrho T a ha mu d hdelta hT hsw C hindex Q hsynth
      hspecial hd hQ hsrc hn)).2

end LocalRelations

/-- All-field, all-group closure of local VIII.1 (1) and (2) for the actual `κ`. -/
def RationalFourierInversionGlobalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom],
    RationalLocalFourierInversionStatement.{u, uV} G

/-- All-field, all-group closure of the local unquotiented formula (2). -/
def RationalUnquotientedReconstructionGlobalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom],
    RationalLocalUnquotientedReconstructionStatement.{u, uV} G

/-- All-field, all-group closure of the local zero case of (2). -/
def RationalFourierInjectivityGlobalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom],
    RationalLocalFourierInjectivityStatement.{u, uV} G

/-- The zero case of VIII.1 (2) for every connected reductive group of relative semisimple rank strictly
below `n`, measured with a maximal split torus. The premise names only lower-rank groups. -/
def RationalStrictlyLowerRankFourierInjectivityStatement (n : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    relativeRootRank i < n →
      RationalLocalFourierInjectivityStatement.{u, uV} G

/-- Increasing the strict rank bound adds requirements. -/
theorem rationalStrictlyLowerRankFourierInjectivity_mono {n m : ℕ} (hnm : n ≤ m)
    (h : RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} m) :
    RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} n := by
  intro F _ _ _ _ G _ _ hG T i hi hlt
  exact h F G hG T i hi (lt_of_lt_of_le hlt hnm)

/-- There is no group of relative semisimple rank strictly below zero. -/
theorem rationalStrictlyLowerRankFourierInjectivity_zero :
    RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} 0 := by
  intro F _ _ _ _ G _ _ hG T i hi hlt
  exact (Nat.not_lt_zero _ hlt).elim

/-- The global target is the conjunction of all strict rank bounds. -/
theorem rationalFourierInjectivityGlobal_iff_all_rank_bounds :
    RationalFourierInjectivityGlobalStatement.{u, uV} ↔
      ∀ n, RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} n := by
  constructor
  · intro h _ F _ _ _ _ G _ _ hG _ _ _ _
    exact h F G
  · intro h F _ _ _ _ G _ _ hG
    have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    obtain ⟨T, i, _, hi, _⟩ := RationalPointFamily.exists_maximalSplitTorus_genericCocharacter hG
    exact h (relativeRootRank i + 1) F G hG T i hi (Nat.lt_succ_self _) hG

/-- The unquotiented formula VIII.1 (2) for every connected reductive group of relative semisimple rank strictly
below `n`, measured with a maximal split torus. The premise names only lower-rank groups. -/
def RationalStrictlyLowerRankUnquotientedReconstructionStatement (n : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    relativeRootRank i < n →
      RationalLocalUnquotientedReconstructionStatement.{u, uV} G

/-- Increasing the strict rank bound adds requirements. -/
theorem rationalStrictlyLowerRankUnquotientedReconstruction_mono {n m : ℕ} (hnm : n ≤ m)
    (h : RationalStrictlyLowerRankUnquotientedReconstructionStatement.{u, uV} m) :
    RationalStrictlyLowerRankUnquotientedReconstructionStatement.{u, uV} n := by
  intro F _ _ _ _ G _ _ hG T i hi hlt
  exact h F G hG T i hi (lt_of_lt_of_le hlt hnm)

/-- There is no group of relative semisimple rank strictly below zero. -/
theorem rationalStrictlyLowerRankUnquotientedReconstruction_zero :
    RationalStrictlyLowerRankUnquotientedReconstructionStatement.{u, uV} 0 := by
  intro F _ _ _ _ G _ _ hG T i hi hlt
  exact (Nat.not_lt_zero _ hlt).elim

/-- The global target is the conjunction of all strict rank bounds. -/
theorem rationalUnquotientedReconstructionGlobal_iff_all_rank_bounds :
    RationalUnquotientedReconstructionGlobalStatement.{u, uV} ↔
      ∀ n, RationalStrictlyLowerRankUnquotientedReconstructionStatement.{u, uV} n := by
  constructor
  · intro h _ F _ _ _ _ G _ _ hG _ _ _ _
    exact h F G
  · intro h F _ _ _ _ G _ _ hG
    have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    obtain ⟨T, i, _, hi, _⟩ := RationalPointFamily.exists_maximalSplitTorus_genericCocharacter hG
    exact h (relativeRootRank i + 1) F G hG T i hi (Nat.lt_succ_self _) hG

section Specialization

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

/-- Apply the strict-rank premise at one connected reductive group. -/
theorem rationalLocalFourierInjectivity_of_rank_lt {n : ℕ}
    (h : RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} n)
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hlt : haveI := hG.isAffineHom; relativeRootRank i < n) :
    haveI := hG.isAffineHom
    RationalLocalFourierInjectivityStatement.{u, uV} G :=
  h F G hG T i hi hlt

/-- Every closed reductive model of a literal proper semistandard Levi lies within the
strict-rank premise at the ambient rank, by the proved rank decrease
`semistandardProperLeviRank` and the inherited maximal split torus. No assertion for
the ambient group occurs. -/
theorem rationalLocalFourierInjectivity_properLevi_of_lowerRank
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (h : haveI := hG.isAffineHom
      RationalStrictlyLowerRankFourierInjectivityStatement.{u, uV} (relativeRootRank i))
    (p : SemistandardSpectralIndex i) (hp : p.parabolic ≠ ⊤)
    (m : RationalSemistandard.LeviModel p) :
    haveI := m.reductive.isAffineHom
    haveI := m.reductive.smooth
    RationalLocalFourierInjectivityStatement.{u, uV} m.scheme := by
  let := hG.isAffineHom
  let := m.reductive.isAffineHom
  let : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
  let := m.reductive.smooth
  exact h F m.scheme m.reductive T
    (semistandardLeviSplitTorus p m.represents)
    (isMaximalSplitTorus_semistandardLeviSplitTorus p m.represents m.closed hi)
    (semistandardProperLeviRank F G hG T i hi p hp m.scheme m.inclusion m.represents m.closed
      m.reductive)

/-- Apply the strict-rank premise at one connected reductive group. -/
theorem rationalLocalUnquotientedReconstruction_of_rank_lt {n : ℕ}
    (h : RationalStrictlyLowerRankUnquotientedReconstructionStatement.{u, uV} n)
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hlt : haveI := hG.isAffineHom; relativeRootRank i < n) :
    haveI := hG.isAffineHom
    RationalLocalUnquotientedReconstructionStatement.{u, uV} G :=
  h F G hG T i hi hlt

/-- Every closed reductive model of a literal proper semistandard Levi lies within the
strict-rank premise at the ambient rank, by the proved rank decrease
`semistandardProperLeviRank` and the inherited maximal split torus. No assertion for
the ambient group occurs. -/
theorem rationalLocalUnquotientedReconstruction_properLevi_of_lowerRank
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (h : haveI := hG.isAffineHom
      RationalStrictlyLowerRankUnquotientedReconstructionStatement.{u, uV} (relativeRootRank i))
    (p : SemistandardSpectralIndex i) (hp : p.parabolic ≠ ⊤)
    (m : RationalSemistandard.LeviModel p) :
    haveI := m.reductive.isAffineHom
    haveI := m.reductive.smooth
    RationalLocalUnquotientedReconstructionStatement.{u, uV} m.scheme := by
  let := hG.isAffineHom
  let := m.reductive.isAffineHom
  let : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
  let := m.reductive.smooth
  exact h F m.scheme m.reductive T
    (semistandardLeviSplitTorus p m.represents)
    (isMaximalSplitTorus_semistandardLeviSplitTorus p m.represents m.closed hi)
    (semistandardProperLeviRank F G hG T i hi p hp m.scheme m.inclusion m.represents m.closed
      m.reductive)

end Specialization

end Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion
