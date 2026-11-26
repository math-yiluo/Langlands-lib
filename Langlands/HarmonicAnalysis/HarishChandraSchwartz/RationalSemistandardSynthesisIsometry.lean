import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariantSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationFormula
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacketFourier

/-! # Waldspurger VII.2.5: the isometry target for the actual invariant synthesis

The first assertion of Theorem VII.2.5 of Waldspurger (2003): the weighted
synthesis `κ` on the invariant finite-support spectral space carries the
source-normalized integral Hermitian form to the integral pairing on `G`. The
target is stated for the actual synthesis `invariantSynthesis` and the actual
form `invariantGlobalForm`. This module also gives its `L²` formulation, the
norm-square formula, the target in the association-representative form of
Remark VII.2.4, and injectivity of `κ` from the isometry and definiteness. -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact (SpecialCompactProperties)
open Langlands.Plancherel.WaldspurgerSourceNormalization (IsSourceCompactAt)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SynthesisIsometry

open GlobalSynthesis GlobalForm

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

local instance isometryCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

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

set_option hygiene false in
set_option quotPrecheck false in
local notation "Invariant" => rationalSemistandardThetaInvariantSections C
set_option hygiene false in
local notation "dg" => RationalDynamicSource.ambientHaar K hK
set_option hygiene false in
local notation "kappa" => invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi hfin
  hK hPK rho hmem hnu hspecial hd hQ
set_option hygiene false in
local notation "form" => invariantGlobalForm hG a ha mu d C.presentation hindex Q K hK C

/-- Waldspurger VII.2.5, first assertion: for any two invariant finite-support
smooth families, the integral over `G` of `conj (κ ψ') · κ ψ` against the source
Haar measure equals the source-normalized integral Hermitian form `B(ψ', ψ)`.
The premises are the preceding inputs that define `κ` (maximal split torus,
geometric fiber finiteness, generic cocharacter, special compact, common compact
and VI.3.1 Schwartz membership), the source compact and quotient Haar
normalizations, the `L²` weight condition of Lemma II.1.5 and nonnegativity of
the actual density. -/
def SynthesisIsometryStatement : Prop :=
  ∀ (hi : IsMaximalSplitTorus i) (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
    (hnu : IsGenericCocharacter i nu)
    (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K) (hQ : ∀ theta, (Q theta).compact = K)
    (hmem : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho),
    IsSourceCompactAt i K.toSubgroup →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho) →
    DensityNonnegative hG a ha mu C.presentation Q →
    ∀ psi' psi : rationalSemistandardThetaInvariantSections C,
      HarishChandraSchwartz.pairing (RationalDynamicSource.ambientHaar K hK)
          (invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi hfin
            hK hPK rho hmem hnu hspecial hd hQ psi')
          (invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi hfin
            hK hPK rho hmem hnu hspecial hd hQ psi) =
        invariantGlobalForm hG a ha mu d C.presentation hindex Q K hK C psi' psi

/-- The same target with the integral replaced by the inner product of the
images in the Hilbert space `L²(G)`, under the existing continuous inclusion
`Space.toL2` of the Schwartz space built from the `L²` weight condition. -/
def SynthesisL2IsometryStatement : Prop :=
  ∀ (hi : IsMaximalSplitTorus i) (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
    (hnu : IsGenericCocharacter i nu)
    (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K) (hQ : ∀ theta, (Q theta).compact = K)
    (hmem : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho),
    IsSourceCompactAt i K.toSubgroup →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    ∀ hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho),
    DensityNonnegative hG a ha mu C.presentation Q →
    ∀ psi' psi : rationalSemistandardThetaInvariantSections C,
      inner ℂ
          (Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw)
            (invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi hfin
              hK hPK rho hmem hnu hspecial hd hQ psi'))
          (Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw)
            (invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi hfin
              hK hPK rho hmem hnu hspecial hd hQ psi)) =
        invariantGlobalForm hG a ha mu d C.presentation hindex Q K hK C psi' psi

section Inputs

variable (hi : IsMaximalSplitTorus i) (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
  (hnu : IsGenericCocharacter i nu)
  (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
  (hd : ∀ t, (d t).compact = K) (hQ : ∀ theta, (Q theta).compact = K)
  (hmem : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)

section Premises

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, (mu t).IsInvInvariant] in
include hspecial hd hQ in
/-- The special compact and the common compact supply the compact premise of
the published VII.2.1–VII.2.3 targets. -/
theorem sourceCompactCompatibility_of_inputs :
    WavePacketPairing.SourceCompactCompatibility hG a ha mu d C.presentation Q (nu := nu) (K := K) :=
  ⟨hspecial, hd, hQ⟩

omit [∀ t, (mu t).IsInvInvariant] in
include hi hfin hnu hspecial hd hQ hmem in
/-- VI.3.1 membership of the weighted sum gives membership of every source
packet: the weighted synthesis of a family supported at one index is the
packet times the positive source coefficient. -/
theorem componentSchwartzMembership_of_schwartzMembership :
    WavePacketPairing.ComponentSchwartzMembershipStatement hG a ha mu d C.presentation hindex Q
      hK hPK rho := by
  intro theta v
  have hsingle := hmem hfin hi hnu hspecial hd hQ (rationalSemistandardThetaSingle a ha mu d theta v)
  have heq : weightedSynthesis hG a ha mu d C.presentation hindex Q K hK
      (rationalSemistandardThetaSingle a ha mu d theta v) =
      (sourceWeight hG C.presentation K hK theta.1 : ℂ) •
        componentPacket hG a ha mu d C.presentation hindex Q theta v := by
    change (∑ᶠ s, ((sourceWeight hG C.presentation K hK s.1 : ℂ) •
        componentPacket hG a ha mu d C.presentation hindex Q s)
          (rationalSemistandardThetaComponent a ha mu d s
            (rationalSemistandardThetaSingle a ha mu d theta v))) = _
    rw [finsum_eq_single _ theta (fun s hs => by
        rw [rationalSemistandardThetaComponent_single_ne a ha mu d hs, map_zero]),
      rationalSemistandardThetaComponent_single]
    rfl
  have hpos : (sourceWeight hG C.presentation K hK theta.1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (SourceConstants.unquotientedWeight_pos (C.presentation theta.1) K hK hi hfin).ne'
  rw [heq] at hsingle
  have hscaled := Submodule.smul_mem _ ((sourceWeight hG C.presentation K hK theta.1 : ℂ)⁻¹) hsingle
  rwa [smul_smul, inv_mul_cancel₀ hpos, one_smul] at hscaled

omit [∀ t, (mu t).IsInvInvariant] in
/-- Conversely, membership of every source packet gives the VI.3.1 membership
of every weighted synthesis, by the finite sum over the literal support. -/
theorem schwartzMembership_of_componentSchwartzMembership
    (h : WavePacketPairing.ComponentSchwartzMembershipStatement hG a ha mu d C.presentation hindex Q
      hK hPK rho) :
    SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho := by
  intro _ _ _ _ _ _ f
  classical
  rw [weightedSynthesis_eq_sum]
  exact Submodule.sum_mem _ fun theta _ => Submodule.smul_mem _ _ (h theta _)

end Premises

section Hilbert

variable (hsw : SquareIntegrableWeight dg (rationalXi hK hPK) (rationalHeight (F := F) rho))

omit [∀ t, (mu t).IsInvInvariant] in
include hsw in
/-- The integrand of the VII.2.5 integral is integrable for the source Haar
measure, by the `L²` theory of the Schwartz space. -/
theorem integrable_conj_synthesis_mul (psi' psi : Invariant) :
    Integrable (fun g => conj (kappa psi' g) * kappa psi g) dg :=
  Space.integrable_conj_mul (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi') (kappa psi)

omit [∀ t, (mu t).IsInvInvariant] in
/-- The integral pairing of two synthesized functions is the inner product
of their images in `L²(G)`. -/
theorem inner_toL2_synthesis (psi' psi : Invariant) :
    inner ℂ (Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi')) (Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi)) =
      HarishChandraSchwartz.pairing dg (kappa psi') (kappa psi) :=
  Space.inner_toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi') (kappa psi)

omit [∀ t, (mu t).IsInvInvariant] in
/-- The diagonal integral is the square of the `L²` norm. -/
theorem pairing_synthesis_self (psi : Invariant) :
    HarishChandraSchwartz.pairing dg (kappa psi) (kappa psi) =
      ((‖Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi)‖ ^ 2 : ℝ) : ℂ) :=
  Space.pairing_self (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi)

end Hilbert

variable (hcompact : IsSourceCompactAt i K.toSubgroup)
  (hhaar : ∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p)
  (hsw : SquareIntegrableWeight dg (rationalXi hK hPK) (rationalHeight (F := F) rho))
  (hn : DensityNonnegative hG a ha mu C.presentation Q)

/-- The integral and `L²` formulations of the target are equivalent. -/
theorem synthesisIsometry_iff_l2 :
    SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho ↔
      SynthesisL2IsometryStatement hG a ha mu d hindex C Q hK hPK rho := by
  constructor
  · intro h hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn psi' psi
    exact (inner_toL2_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ
      hmem hsw psi' psi).trans (h hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn psi' psi)
  · intro h hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn psi' psi
    exact (inner_toL2_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ
      hmem hsw psi' psi).symm.trans (h hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn psi' psi)

include hcompact hhaar hsw hn in
/-- The isometry at the displayed inputs, as an equation of the actual integral. -/
theorem pairing_synthesis_eq_form
    (h : SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho) (psi' psi : Invariant) :
    HarishChandraSchwartz.pairing dg (kappa psi') (kappa psi) = form psi' psi :=
  h hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn psi' psi

include hcompact hhaar hsw hn in
/-- The isometry at the displayed inputs, in `L²(G)`. -/
theorem inner_toL2_synthesis_eq_form
    (h : SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho) (psi' psi : Invariant) :
    inner ℂ (Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi')) (Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi)) = form psi' psi :=
  (inner_toL2_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw
    psi' psi).trans
    (pairing_synthesis_eq_form hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem
      hcompact hhaar hsw hn h psi' psi)

include hcompact hhaar hsw hn in
/-- The diagonal norm-square formula: `‖κ ψ‖²_{L²(G)} = B(ψ, ψ)`. -/
theorem norm_sq_toL2_synthesis
    (h : SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho) (psi : Invariant) :
    ((‖Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi)‖ ^ 2 : ℝ) : ℂ) = form psi psi :=
  (pairing_synthesis_self hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw
    psi).symm.trans
    (pairing_synthesis_eq_form hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem
      hcompact hhaar hsw hn h psi psi)

include hcompact hhaar hsw hn in
/-- The real form of the norm-square formula. -/
theorem norm_sq_toL2_synthesis_eq_re
    (h : SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho) (psi : Invariant) :
    ‖Space.toL2 (rationalL2Weights K.isOpen hK hPK rho hsw) (kappa psi)‖ ^ 2 = (form psi psi).re := by
  rw [← norm_sq_toL2_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem
    hcompact hhaar hsw hn h psi, Complex.ofReal_re]

include hcompact hhaar hsw hn in
/-- Injectivity of `κ` from the isometry and the definiteness supplied by the
existing positive form `invariantGlobalPositiveForm`, whose inputs are the
published positivity target and the dense positivity of the actual density. -/
theorem invariantSynthesis_injective_of_isometry
    (h : SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho)
    (hpos : PositiveFormStatement hG a ha mu d C.presentation hindex Q K hK)
    (hdense : DensityPositiveDense hG a ha mu C.presentation Q) :
    Function.Injective kappa := by
  intro x y hxy
  let z : Invariant := x + (-1 : ℂ) • y
  have hk : kappa z = 0 := by
    change kappa (x + (-1 : ℂ) • y) = 0
    rw [LinearMap.map_add, LinearMap.map_smul, hxy, neg_one_smul, add_neg_cancel]
  have hz : z = 0 := by
    refine (invariantGlobalPositiveForm hG a ha mu d C.presentation hindex Q K hK C
      hpos hfin hi hn hdense).definite z ?_
    change form z z = 0
    rw [← pairing_synthesis_eq_form hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ
        hmem hcompact hhaar hsw hn h z z, hk]
    simp only [HarishChandraSchwartz.pairing_apply, Space.coe_zero, Pi.zero_apply, map_zero,
      mul_zero, integral_zero]
  have hv := congrArg (fun w : Invariant => w.val.val) hz
  change x.val.val + (-1 : ℂ) • y.val.val = 0 at hv
  rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at hv
  exact Subtype.ext (Subtype.ext hv)

end Inputs

section Association

open Association

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, (mu t).IsInvInvariant] in
/-- The coefficient of an association representative in Remark VII.2.4 is
`c(G|M)^(-2) γ(G|M)^(-1) / |Stab(O,M)|`, where `Stab(O,M)` is the stabilizer of
the orbit in the literal `W(G|M)`. -/
theorem coefficientAtRepresentative_eq (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    coefficientAtRepresentative C K hK t =
      ((SourceConstants.cReal (C.presentation t.1) K hK) ^ 2)⁻¹ *
        (SourceConstants.gammaReal (C.presentation t.1) K hK)⁻¹ /
          (Nat.card (WeylOrbitStabilizer a ha mu t (C.centralizer_le t.1)) : ℝ) := rfl

/-- Theorem VII.2.5 in the association-representative form of Remark VII.2.4:
Remark VII.2.4 supplies the two representative sums, with one actual
representative of each association class and the coefficient
`c(G|M)^(-2) γ(G|M)^(-1) / |Stab(O,M)|`; the isometry between them is the
assertion of Theorem VII.2.5, for every choice of representatives. The premises
are those of `SynthesisIsometryStatement`. -/
def AssociationIsometryStatement : Prop :=
  ∀ (_ : IsMaximalSplitTorus i) (_ : SemistandardSpectralFiberFinitenessStatement.{u})
    (_ : IsGenericCocharacter i nu)
    (_ : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (_ : ∀ t, (d t).compact = K) (_ : ∀ theta, (Q theta).compact = K)
    (_ : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho),
    IsSourceCompactAt i K.toSubgroup →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho) →
    DensityNonnegative hG a ha mu C.presentation Q →
    ∀ (R : Association.Representatives.{u, uV} a ha mu)
      (psi' psi : rationalSemistandardThetaInvariantSections C),
      HarishChandraSchwartz.pairing (RationalDynamicSource.ambientHaar K hK)
          (packetRepresentativeSum C K hK hindex Q R psi')
          (packetRepresentativeSum C K hK hindex Q R psi) =
        formRepresentativeSum C K hK hindex Q R psi' psi

/-- Under the published association formulas, the synthesized function is the
representative sum at every point. -/
theorem synthesis_eq_packetRepresentativeSum
    (hA : AssociationFormulaStatement C K hK hindex Q)
    (hi : IsMaximalSplitTorus i) (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
    (hnu : IsGenericCocharacter i nu)
    (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K) (hQ : ∀ theta, (Q theta).compact = K)
    (hmem : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)
    (R : Association.Representatives.{u, uV} a ha mu) (psi : Invariant) :
    (kappa psi : rationalPoints G → ℂ) = packetRepresentativeSum C K hK hindex Q R psi :=
  funext fun g => (hA R).1 psi g

/-- Given the published association formulas, the unquotiented isometry and the
isometry over association representatives are equivalent. -/
theorem synthesisIsometry_iff_association (hA : AssociationFormulaStatement C K hK hindex Q) :
    SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho ↔
      AssociationIsometryStatement hG a ha mu d hindex C Q hK hPK rho := by
  constructor
  · intro h hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn R psi' psi
    have e' := synthesis_eq_packetRepresentativeSum hG a ha mu d hindex C Q hK hPK rho hA hi hfin
      hnu hspecial hd hQ hmem R psi'
    have e := synthesis_eq_packetRepresentativeSum hG a ha mu d hindex C Q hK hPK rho hA hi hfin
      hnu hspecial hd hQ hmem R psi
    exact (congrArg₂ (HarishChandraSchwartz.pairing dg) e' e).symm.trans
      ((h hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn psi' psi).trans ((hA R).2 psi' psi))
  · intro h hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn psi' psi
    let R := Association.Representatives.ofQuotient.{u, uV} a ha mu
    have e' := synthesis_eq_packetRepresentativeSum hG a ha mu d hindex C Q hK hPK rho hA hi hfin
      hnu hspecial hd hQ hmem R psi'
    have e := synthesis_eq_packetRepresentativeSum hG a ha mu d hindex C Q hK hPK rho hA hi hfin
      hnu hspecial hd hQ hmem R psi
    exact (congrArg₂ (HarishChandraSchwartz.pairing dg) e' e).trans
      ((h hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn R psi' psi).trans
        ((hA R).2 psi' psi).symm)

/-- The conditional implication to Theorem VII.2.5 in the association-representative
form of Remark VII.2.4, through the published transport proof of the association
formulas. Its hypotheses are
exactly those of `associationFormula_of_transport` that are not already
premises of the target; the intrinsic quotient normalization there follows
from the source quotient Haar normalization and the common compact. -/
theorem associationIsometry_of_isometry
    (hD : SemistandardSpectralDynamicCoverageStatement.{u})
    (hI : SourceConstantParabolicIndependenceStatement (i := i) hG)
    (hE : C.CoefficientTransportStatement) (hDensity : C.DensityTransportStatement Q)
    (hForm : C.PairingTransportStatement)
    (h : SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho) :
    AssociationIsometryStatement hG a ha mu d hindex C Q hK hPK rho := by
  intro hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn R psi' psi
  have hquot : SourceMeasure.IntrinsicQuotientNormalization a mu d := by
    intro p
    rw [hd p]
    exact hhaar p
  have hA := associationFormula_of_transport C K hK hindex Q hi hD hfin hI nu hnu hspecial hd hQ
    hE hDensity hquot hForm
  exact (synthesisIsometry_iff_association hG a ha mu d hindex C Q hK hPK rho hA).mp h
    hi hfin hnu hspecial hd hQ hmem hcompact hhaar hsw hn R psi' psi

end Association

end Langlands.HarishChandraSchwartz.RationalSemistandard.SynthesisIsometry
