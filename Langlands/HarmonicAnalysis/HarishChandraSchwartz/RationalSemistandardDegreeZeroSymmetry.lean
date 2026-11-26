import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardDegreeZero
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperSynthesisSymmetry

/-! # Remark VIII.2.2: symmetries of the degree-zero operator -/

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

local instance degreeZeroSymmetryCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance degreeZeroSymmetryParabolicLC (p : SemistandardSpectralIndex i) :
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
local notation "checkC" =>
  Space.check (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)

set_option hygiene false in
local notation "twist" => rationalSchwartzUnitaryTwist hG hKc hPK rho

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
include hS hin in
/-- The proper smoothness witness of the lift: the full component smoothness target at
proper indices. -/
theorem rationalSemistandardDegreeZero_properSmooth (f : Schwartz) (t : Θ) (_ : t.1.IsProper) :
    fourier f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t :=
  rationalSemistandardFourierFamily_mem_componentSpace_of_smoothness hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT hS hin f t

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal] in
include hgeo hcomp hlow in
/-- The proper finite-support witness of the lift: strictly lower-rank local finiteness. -/
theorem rationalSemistandardDegreeZero_properFiniteSupport :
    RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT :=
  rationalProperSemistandardFourierFiniteSupport_of_strictlyLowerRank hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT semistandardProperLeviRank hgeo hcomp hlow

/-- **The subtracted term is the proper Fourier synthesis.** For every proper smoothness and
finite-support witness, `°f(g) = f(g) - properFourierSynthesis f g`. -/
theorem rationalSemistandardDegreeZero_apply_eq_sub_properFourierSynthesis
    (hsm : ∀ (f : Schwartz) (t : Θ), t.1.IsProper →
      fourier f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d t)
    (hfs : RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT) (f : Schwartz) (g : rationalPoints G) :
    degreeZero f g = f g - GlobalSynthesis.properFourierSynthesis hG hi hnu hKc hPK rho
      a ha muM d rs hindex Q K0 hK0 hsw hdelta hT hsm hfs f g := rfl

/-- **Remark VIII.2.2 for the actual operator.** Given the three induced-character
comparisons (`SemistandardInducedCharacterSymmetryStatement`: VII.1.1(iii) for the check,
the conjugate and the unitary twist) and the orbit comparisons at proper indices
(`GlobalSynthesis.ProperOrbitSymmetryStatement`: measure-preserving orbit transports, equal
formal degrees, invariance of the density under the transports, including
`μ(ω ⊗ χ) = μ(ω)`, and reality of the density), the operator commutes with
`f ↦ fˇ`, with pointwise complex conjugation and with multiplication by every unitary
unramified character of `G`. -/
def RationalSemistandardDegreeZeroSymmetryStatement : Prop :=
  SemistandardInducedCharacterSymmetryStatement hG hi hnu hKc hPK rho a ha muM d hsw hT →
    GlobalSynthesis.ProperOrbitSymmetryStatement a ha muM d hindex hG rs Q →
      ∀ f : Schwartz,
        checkC (degreeZero f) = degreeZero (checkC f) ∧
        Space.complexConj (degreeZero f) = degreeZero (Space.complexConj f) ∧
        ∀ χ : rationalUnitaryUnramifiedCharacters G, twist χ (degreeZero f) = degreeZero (twist χ f)

/-- The three identities reduce, pointwise, to the three comparisons of the subtracted proper
synthesis (`GlobalSynthesis.properFourierSynthesis_symmetry`). -/
theorem rationalSemistandardDegreeZero_symmetry :
    RationalSemistandardDegreeZeroSymmetryStatement a ha muM d hG C hi hnu hKc hPK rho hsw hdelta
      hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ := by
  intro hchar horbit f
  have hsm := rationalSemistandardDegreeZero_properSmooth a ha muM d hG hi hnu hKc hPK rho hsw
    hdelta hT hS hin
  have hfs := rationalSemistandardDegreeZero_properFiniteSupport a ha muM d hG hi hnu hKc hPK rho
    hsw hdelta hT hgeo hcomp hlow
  have hsym := GlobalSynthesis.properFourierSynthesis_symmetry hG hi hnu hKc hPK rho a ha muM d rs
    hindex Q K0 hK0 hsw hdelta hT hsm hfs hchar horbit f
  have happ := rationalSemistandardDegreeZero_apply_eq_sub_properFourierSynthesis a ha muM d hG C
    hi hnu hKc hPK rho hsw hdelta hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber
    hmem hspecial hd hQ hsm hfs
  refine ⟨Space.ext fun g => ?_, Space.ext fun g => ?_, fun χ => Space.ext fun g => ?_⟩
  · change degreeZero f g⁻¹ = degreeZero (checkC f) g
    rw [happ, happ, (hsym g).1]
    rfl
  · change conj (degreeZero f g) = degreeZero (Space.complexConj f) g
    rw [happ, happ, map_sub, (hsym g).2.1]
    rfl
  · rw [rationalSchwartzUnitaryTwist_apply, happ, happ, sub_mul, (hsym g).2.2 χ,
      rationalSchwartzUnitaryTwist_apply]

section Laws

variable (hchar : SemistandardInducedCharacterSymmetryStatement hG hi hnu hKc hPK rho
    a ha muM d hsw hT)
  (horbit : GlobalSynthesis.ProperOrbitSymmetryStatement a ha muM d hindex hG rs Q)

include hchar horbit

/-- The check law of `RationalCuspidalUnit` for the operator. -/
theorem rationalSemistandardDegreeZero_checkLaw :
    RationalDegreeZeroCheckLaw hKc hPK rho degreeZero := by
  intro f f' hf' x
  have hf'eq : f' = checkC f := Space.ext hf'
  subst hf'eq
  have h := (rationalSemistandardDegreeZero_symmetry a ha muM d hG C hi hnu hKc hPK rho hsw hdelta
    hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ
    hchar horbit f).1
  rw [← h]
  rfl

/-- The conjugation law of `RationalCuspidalUnit` for the operator. -/
theorem rationalSemistandardDegreeZero_conjLaw :
    RationalDegreeZeroConjLaw hKc hPK rho degreeZero := by
  intro f f' hf' x
  have hf'eq : f' = Space.complexConj f := Space.ext hf'
  subst hf'eq
  have h := (rationalSemistandardDegreeZero_symmetry a ha muM d hG C hi hnu hKc hPK rho hsw hdelta
    hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ
    hchar horbit f).2.1
  rw [← h]
  rfl

/-- The unitary-twist law of `RationalCuspidalUnit` for the operator. -/
theorem rationalSemistandardDegreeZero_twistLaw :
    RationalDegreeZeroTwistLaw hKc hPK rho degreeZero := by
  intro χ hχ f f' hf' x
  have hf'eq : f' = twist ⟨χ, hχ⟩ f :=
    Space.ext fun y => by rw [hf', rationalSchwartzUnitaryTwist_apply]
  subst hf'eq
  have h := (rationalSemistandardDegreeZero_symmetry a ha muM d hG C hi hnu hKc hPK rho hsw hdelta
    hT hgeo hcomp hlow hS hin hsplit hcov rs hindex Q K0 hK0 hfiber hmem hspecial hd hQ
    hchar horbit f).2.2 ⟨χ, hχ⟩
  rw [← h, rationalSchwartzUnitaryTwist_apply]

end Laws

end Langlands.HarishChandraSchwartz
