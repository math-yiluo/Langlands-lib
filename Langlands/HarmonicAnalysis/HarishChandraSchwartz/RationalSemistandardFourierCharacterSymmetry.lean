import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalUnit
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalConvolution
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedFourierFamily
import Langlands.Representation.Unitary.ConjugateSpace

/-! # The induced Schwartz character comparisons in VIII.2.2 -/

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance fourierCharacterCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance fourierCharacterParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {nu : cocharacterLattice S} (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

set_option hygiene false in
local notation "C" => RationalSchwartzSpace hKc hPK rho

/-- The existing Schwartz twist in the canonical coordinates of the actual
ambient unitary unramified group. -/
def rationalSchwartzUnitaryTwist (χ : rationalUnitaryUnramifiedCharacters G) : C →ₗ[ℂ] C :=
  Space.twist (rationalValuationCoordinates_mul G hG)
    (K₀ := ⟨K, hKc⟩)
    (fun k hk => by
      have hmem : k ∈ (rationalValuationImageProjection G).ker := by
        rw [rationalValuationImageProjection_ker]
        exact compactSubgroup_le_rationalCommonNormKernel G K hKc hk
      rw [MonoidHom.mem_ker] at hmem
      funext j
      simp [rationalValuationCoordinates_apply, hmem])
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG χ)

@[simp] theorem rationalSchwartzUnitaryTwist_apply (χ : rationalUnitaryUnramifiedCharacters G)
    (f : C) (g : rationalPoints G) :
    rationalSchwartzUnitaryTwist hG hKc hPK rho χ f g = f g * (χ.val g : ℂ) := by
  change f g * HarmonicAnalysis.TorusFourier.torusCharacter (rationalValuationCoordinates G hG g)
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG χ) = _
  congr 1
  simpa only [ContinuousMulEquiv.symm_apply_apply] using
    (rationalUnitaryUnramifiedCharacter_apply G hG
      (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG χ) g).symm

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (muM : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (muM t).IsHaarMeasure] [∀ t, (muM t).IsInvInvariant]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))

set_option hygiene false in
local notation "Rep(" p ")" => IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)
set_option hygiene false in
local notation "DS(" p "," A ")" => IsSquareIntegrableModCentralSubgroup
  ((chosenLeviModel p).splitCenter (a p))
  ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) (A).obj.representation (muM p)

variable (hT : ∀ (p : SemistandardSpectralIndex i) (A : Rep(p)), DS(p,A) →
  HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
    ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

/-- The trace of the actual finite-rank normalized induced Schwartz action. -/
def semistandardInducedSchwartzCharacter
    (p : SemistandardSpectralIndex i) (A : Rep(p)) (hsqA : DS(p,A)) : C →L[ℂ] ℂ :=
  schwartzCharacter (rationalL2Weights K.isOpen hKc hPK rho hsw)
    (CompactInduction.induced_isAdmissible (decomposition p) (isClosed_radical p)
      (d p).compact (d p).isCompact (d p).factorization_mem A.obj (d p).projection_continuous hsqA.1)
    (hT p A hsqA)

set_option hygiene false in
local notation "char" => semistandardInducedSchwartzCharacter hKc hPK rho a ha muM d hsw hT
set_option hygiene false in
local notation "λg" => Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) 1
set_option hygiene false in
local notation "checkC" =>
  Space.check (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)

/-- The check-character comparison of VIII.2.2 for the smooth contragredient. -/
def SemistandardInducedCharacterCheckStatement : Prop :=
  ∀ (p : SemistandardSpectralIndex i) (A B : Rep(p)) (hsqA : DS(p,A)) (hsqB : DS(p,B)),
    Nonempty ((smoothContragredient A.obj.representation).Equiv B.obj.representation) →
    ∀ (f : C) (g : rationalPoints G),
      char p A hsqA (λg g⁻¹ (checkC f)) = char p B hsqB (λg g f)

/-- The conjugate-character comparison of VIII.2.2 on the actual conjugate
complex representation. -/
def SemistandardInducedCharacterConjStatement : Prop :=
  ∀ (p : SemistandardSpectralIndex i) (A B : Rep(p)) (hsqA : DS(p,A)) (hsqB : DS(p,B)),
    Nonempty ((ConjSpace.rep A.obj.representation).Equiv B.obj.representation) →
    ∀ (f : C) (g : rationalPoints G),
      conj (char p A hsqA (λg g (checkC f))) =
        char p B hsqB (λg g (checkC (Space.complexConj f)))

/-- The twist-character comparison of VIII.2.2 with the ambient character
restricted to the literal Levi. -/
def SemistandardInducedCharacterTwistStatement : Prop :=
  ∀ (χ : rationalUnitaryUnramifiedCharacters G) (p : SemistandardSpectralIndex i)
    (A B : Rep(p)) (hsqA : DS(p,A)) (hsqB : DS(p,B)),
    Nonempty ((Langlands.twist (χ.val.toMonoidHom.comp (levi p).subtype)
      A.obj.representation).Equiv B.obj.representation) →
    ∀ (f : C) (g : rationalPoints G),
      (χ.val g : ℂ) * char p A hsqA (λg g (checkC f)) =
        char p B hsqB (λg g (checkC (rationalSchwartzUnitaryTwist hG hKc hPK rho χ f)))

/-- The three actual induced character comparisons used in VIII.2.2. -/
def SemistandardInducedCharacterSymmetryStatement : Prop :=
  SemistandardInducedCharacterCheckStatement hG hi hnu hKc hPK rho a ha muM d hsw hT ∧
  SemistandardInducedCharacterConjStatement hG hi hnu hKc hPK rho a ha muM d hsw hT ∧
  SemistandardInducedCharacterTwistStatement hG hi hnu hKc hPK rho a ha muM d hsw hT

end Langlands.HarishChandraSchwartz.RationalSemistandard
