import Langlands.GroupScheme.Rational.SemistandardProperLeviRankProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariantSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSynthesisTranslation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalUnit

/-! # The degree-zero operator `f ↦ °f` of Waldspurger VIII.2 -/

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

local instance degreeZeroCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance degreeZeroParabolicLC (p : SemistandardSpectralIndex i) :
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

section ProperPart

variable {a ha muM d hG}

omit [∀ t, (muM t).IsInvInvariant] in
/-- The proper part of a Weyl-invariant family is Weyl invariant. An actual Weyl
transport relates the source index to the target index of each comparison arrow,
so the two indices are proper together (`Association.Associated.isProper_iff`). -/
theorem IsWeylInvariant.properPart (hsplit : SemistandardProperSplitComparisonStatement.{u})
    (hi : IsMaximalSplitTorus i) {f : RationalSemistandardThetaSections.{u, uV} a ha muM}
    (hf : IsWeylInvariant C f) : IsWeylInvariant C (properPart f) := by
  intro t q n A
  have hp : t.1.IsProper ↔ (C.target t q n).1.IsProper :=
    Association.Associated.isProper_iff a ha muM hsplit hG hi ⟨_, C.target_transports t q n⟩
  by_cases ht : t.1.IsProper
  · rw [rationalSemistandardThetaProperPart_apply_of_mem (show C.target t q n ∈
        rationalSemistandardThetaProper.{u, uV} a ha muM from hp.mp ht),
      rationalSemistandardThetaProperPart_apply_of_mem
        (show t ∈ rationalSemistandardThetaProper.{u, uV} a ha muM from ht)]
    exact hf t q n A
  · rw [rationalSemistandardThetaProperPart_apply_of_not_mem (show C.target t q n ∉
        rationalSemistandardThetaProper.{u, uV} a ha muM from mt hp.mpr ht),
      rationalSemistandardThetaProperPart_apply_of_not_mem
        (show t ∉ rationalSemistandardThetaProper.{u, uV} a ha muM from ht)]
    exact (C.fiberComparison t q n A).map_zero.symm

end ProperPart

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

/-! ## The finite-support smooth invariant lift of the proper truncation -/

section Lift

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

/-- **The invariant lift `ψ` of VIII.2.** The proper Fourier truncation of `f`
(`ψ_f[O,P]` for `P ≠ G`, zero for `P = G`) as an element of the actual invariant
finite-support smooth carrier. Finite support uses only strictly lower-rank local
finiteness, through the proved proper-Levi rank decrease `semistandardProperLeviRank`, the
normal-level comparison and geometric finiteness of the index; smoothness uses the full
component smoothness target; invariance uses VII.1.4 in the form `hcov` and the structural
proper/group split comparison. -/
def rationalSemistandardProperFourierInvariant :
    Schwartz →ₗ[ℂ] rationalSemistandardThetaInvariantSections C :=
  (rationalSemistandardProperFourierSmooth hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
    semistandardProperLeviRank hgeo hcomp hlow hS hin).codRestrict
    (rationalSemistandardThetaInvariantSections C)
    (fun f => IsWeylInvariant.properPart C hsplit hi (hcov f))

@[simp] theorem rationalSemistandardProperFourierInvariant_val_val (f : Schwartz) :
    (rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov f).val.val = properFourier f := rfl

omit [∀ t, (muM t).IsInvInvariant] in
/-- Two elements of the invariant carrier with the same underlying family agree. -/
theorem rationalSemistandardThetaInvariantSections_ext
    {v w : rationalSemistandardThetaInvariantSections C} (h : v.val.val = w.val.val) : v = w :=
  Subtype.ext (Subtype.ext h)

/-- Any element of the invariant carrier whose underlying family is the proper truncation of
`f` is the lift of `f`: the lift does not depend on the support and smoothness witnesses. -/
theorem rationalSemistandardProperFourierInvariant_eq_of_val (f : Schwartz)
    (v : rationalSemistandardThetaInvariantSections C) (hv : v.val.val = properFourier f) :
    rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov f = v :=
  rationalSemistandardThetaInvariantSections_ext a ha muM d hG C hv.symm

/-- The lift is supported in the proper part `Θ - Θ_G`. -/
theorem rationalSemistandardProperFourierInvariant_support_subset (f : Schwartz) :
    rationalSemistandardThetaSupport.{u, uV} a ha muM
        (rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
          hgeo hcomp hlow hS hin hsplit hcov f).val.val ⊆
      rationalSemistandardThetaProper.{u, uV} a ha muM := by
  rw [rationalSemistandardProperFourierInvariant_val_val, rationalSemistandardProperFourier_support]
  exact Set.inter_subset_right

/-- At a proper index the lift is the actual Fourier component `ψ_f[O,P]`. -/
theorem rationalSemistandardProperFourierInvariant_apply_of_isProper (f : Schwartz) {t : Θ}
    (ht : t.1.IsProper) :
    (rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov f).val.val t = fourier f t :=
  rationalSemistandardProperFourier_apply_of_isProper hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
    f ht

/-- At an index with `P = G` the lift is zero. -/
theorem rationalSemistandardProperFourierInvariant_apply_of_parabolic_eq_top (f : Schwartz)
    {t : Θ} (ht : t.1.parabolic = ⊤) :
    (rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
      hgeo hcomp hlow hS hin hsplit hcov f).val.val t = 0 :=
  rationalSemistandardProperFourier_apply_of_parabolic_eq_top hG hi hnu hKc hPK rho hsw a ha muM d
    hdelta hT f ht

/-- The lift intertwines two-sided translation of `f` with the actual `G × G` action on the
invariant carrier. -/
theorem rationalSemistandardProperFourierInvariant_translate (g1 g2 : rationalPoints G)
    (f : Schwartz) :
    rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
        hgeo hcomp hlow hS hin hsplit hcov
        (Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f) =
      rationalSemistandardThetaInvariantRepresentation C (g1, g2)
        (rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
          hgeo hcomp hlow hS hin hsplit hcov f) :=
  rationalSemistandardThetaInvariantSections_ext a ha muM d hG C
    (rationalSemistandardProperFourier_translate hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
      g1 g2 f)

/-! ## The operator -/

variable [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal]

variable (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
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
local notation "kappa" =>
  GlobalSynthesis.invariantSynthesis hG a ha muM d rs hindex Q K0 hK0 C hi hfiber hKc hPK rho
    hmem hnu hspecial hd hQ

set_option hygiene false in
local notation "lift" =>
  rationalSemistandardProperFourierInvariant a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
    hgeo hcomp hlow hS hin hsplit hcov

/-- **Waldspurger's `°f = f - κ(ψ)` (VIII.2).** The complex-linear operator on the actual
rational Schwartz space subtracting from `f` the actual weighted synthesis `κ` of the invariant
lift of the proper Fourier truncation of `f`. -/
def rationalSemistandardDegreeZero : Schwartz →ₗ[ℂ] Schwartz :=
  LinearMap.id - (kappa).comp (lift)

set_option hygiene false in
local notation "degreeZero" =>
  rationalSemistandardDegreeZero a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
    hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ

/-- The defining formula `°f = f - κ(ψ)`. -/
theorem rationalSemistandardDegreeZero_apply (f : Schwartz) :
    degreeZero f = f - kappa (lift f) := rfl

/-- The defining formula pointwise, with the raw weighted synthesis. -/
theorem rationalSemistandardDegreeZero_apply_apply (f : Schwartz) (g : rationalPoints G) :
    degreeZero f g =
      f g - GlobalSynthesis.weightedSynthesis hG a ha muM d rs hindex Q K0 hK0
        (lift f).val g := rfl

/-- **Independence of the witnesses.** For every element `v` of the invariant carrier whose
underlying family is the proper truncation of `f`, `°f = f - κ(v)`. -/
theorem rationalSemistandardDegreeZero_eq_sub (f : Schwartz)
    (v : rationalSemistandardThetaInvariantSections C) (hv : v.val.val = properFourier f) :
    degreeZero f = f - kappa v := by
  rw [rationalSemistandardDegreeZero_apply,
    rationalSemistandardProperFourierInvariant_eq_of_val a ha muM d hG C hi hnu hKc hPK rho hsw
      hdelta hT hgeo hcomp hlow hS hin hsplit hcov f v hv]

/-- The operator fixes every `f` whose proper Fourier truncation vanishes. -/
theorem rationalSemistandardDegreeZero_eq_self_of_properFourier_eq_zero (f : Schwartz)
    (hf : properFourier f = 0) : degreeZero f = f := by
  rw [rationalSemistandardDegreeZero_eq_sub a ha muM d hG C hi hnu hKc hPK rho hsw hdelta hT
    hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ f 0
    hf.symm, map_zero, sub_zero]

/-- **Rank zero.** In relative semisimple rank zero every semistandard parabolic is `G`, the
proper truncation vanishes and the operator is the identity. -/
theorem rationalSemistandardDegreeZero_eq_id_of_rank_zero (hzero : relativeRootRank i = 0) :
    degreeZero = LinearMap.id :=
  LinearMap.ext fun f =>
    rationalSemistandardDegreeZero_eq_self_of_properFourier_eq_zero a ha muM d hG C hi hnu hKc hPK
      rho hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial
      hd hQ f (by
        rw [rationalSemistandardProperFourier_eq_zero_of_rank_zero hG hi hnu hKc hPK rho hsw
          a ha muM d hdelta hT semistandardProperLeviRank hzero]
        rfl)

/-- **Two-sided translation.** `°(ρ(g₁) λ(g₂) f) = ρ(g₁) λ(g₂) °f`: the proper truncation is
equivariant for the actual `G × G` actions and the weighted synthesis intertwines that action
with translation (`GlobalSynthesis.weightedSynthesis_translate`). -/
theorem rationalSemistandardDegreeZero_translate (g1 g2 : rationalPoints G) (f : Schwartz) :
    degreeZero (Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f) =
      Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 (degreeZero f) := by
  have hlift : (lift (Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f)).val =
      rationalSemistandardThetaSmoothRepresentation.{u, uV} a ha muM d (g1, g2) (lift f).val :=
    congrArg Subtype.val (rationalSemistandardProperFourierInvariant_translate a ha muM d hG C hi hnu
      hKc hPK rho hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov g1 g2 f)
  apply Space.ext
  intro x
  rw [rationalSemistandardDegreeZero_apply_apply, hlift,
    GlobalSynthesis.weightedSynthesis_translate a ha muM d hG rs hindex Q K0 hK0 (g1, g2)]
  rfl

/-- The translation law of `RationalCuspidalUnit` for the operator. -/
theorem rationalSemistandardDegreeZero_translationLaw :
    RationalDegreeZeroTranslationLaw hKc hPK rho degreeZero := by
  intro x y f f' hf' z
  have hf'eq : f' = Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) y x⁻¹ f :=
    Space.ext fun w => by rw [hf', Space.translate_apply, inv_inv]
  rw [hf'eq, rationalSemistandardDegreeZero_translate, Space.translate_apply, inv_inv]

end Lift

end Langlands.HarishChandraSchwartz
