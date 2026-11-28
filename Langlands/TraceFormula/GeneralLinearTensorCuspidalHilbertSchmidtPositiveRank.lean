import Langlands.TraceFormula.CompactSmoothAdelicGLTestConvolution
import Langlands.Automorphic.GroupSchemeCuspidalConvolutionCompact
import Langlands.Automorphic.GeneralLinearCanonicalUniformComparison
import Langlands.GroupScheme.GeneralLinearSmoothFunctions
import Langlands.Global.AdelicGLInverseTranspose

/-!
# Hilbert–Schmidt cuspidal operators of tensor tests in positive rank

See `GeneralLinearTensorCuspidalHilbertSchmidtPositiveRank.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance tensorHSIsAffine : IsAffine
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance tensorHSSmooth :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

/-- A compactly supported locally constant function on `GL_n(𝔸_f)` is invariant under left and
right translation by some open subgroup. -/
theorem CompactFiniteGLTest.exists_openSubgroup_biInvariant (b : CompactFiniteGLTest K n) :
    ∃ L : OpenSubgroup (FiniteAdelicGL K n), ∀ k ∈ L, ∀ x,
      b.val (k * x) = b.val x ∧ b.val (x * k) = b.val x := by
  have := finiteAdelicGL_t2Space K n
  have := finiteAdelicGL_totallyDisconnectedSpace' K n
  let b' : HarmonicAnalysis.SchwartzBruhat (FiniteAdelicGL K n) :=
    ⟨b.val, b.val.isLocallyConstant, b.property⟩
  obtain ⟨L, -, -, hL⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance
    (FiniteAdelicGL K n) {b'} ⊤
  exact ⟨L, fun k hk x => ⟨(hL b' (Finset.mem_singleton_self _)).1 ⟨k, hk⟩ x,
    (hL b' (Finset.mem_singleton_self _)).2 ⟨k, hk⟩ x⟩⟩

/-- The tensor test pulled back to group-scheme points translates through `ofFinite` on either
side by the finite matrix factor. -/
theorem adelicTestTensor_ofFinite_mul (a : ArchimedeanGL.SmoothCompactKernel K n)
    (b : CompactFiniteGLTest K n) (y : FiniteAdelicGL K n) (x : AdelicGL K n) :
    adelicTestTensor K n a b (AdelicGL.ofFinite K n y * x) =
        ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n x) *
          b.val (y * AdelicGL.finite K n x) ∧
      adelicTestTensor K n a b (x * AdelicGL.ofFinite K n y) =
        ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n x) *
          b.val (AdelicGL.finite K n x * y) := by
  constructor
  · change ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n _) *
      b.val (AdelicGL.finite K n _) = _
    rw [map_mul (AdelicGL.infinite K n), map_mul (AdelicGL.finite K n), AdelicGL.infinite_ofFinite,
      AdelicGL.finite_ofFinite, one_mul]
  · change ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n _) *
      b.val (AdelicGL.finite K n _) = _
    rw [map_mul (AdelicGL.infinite K n), map_mul (AdelicGL.finite K n), AdelicGL.infinite_ofFinite,
      AdelicGL.finite_ofFinite, mul_one]

/-- **Tensor tests are adelic test functions.** The tensor of a smooth compactly supported
archimedean kernel and a compactly supported locally constant finite test, read on the adelic
points of the group scheme `GL_n`, is smooth with plot-smooth infinite slices, compactly
supported, and bi-invariant under an open subgroup of the finite adelic points. -/
theorem isAdelicTestFunction_adelicTestTensor (a : ArchimedeanGL.SmoothCompactKernel K n)
    (b : CompactFiniteGLTest K n) :
    IsAdelicTestFunction K GLₙ
      (fun g => adelicTestTensor K n a b (GeneralLinearGroupPoints.adelicHomeomorph K n g)) := by
  let E := GeneralLinearGroupPoints.adelicHomeomorph K n
  let fH := GeneralLinearGroupPoints.finiteHomeomorph K n
  let T := CompactSmoothAdelicGLTest.tensor K n a b
  have hcont : Continuous (adelicTestTensor K n a b) := CompactSmoothAdelicGLTest.continuous K n T
  have hcpt : HasCompactSupport (adelicTestTensor K n a b) :=
    CompactSmoothAdelicGLTest.hasCompactSupport K n T
  obtain ⟨L, hL⟩ := CompactFiniteGLTest.exists_openSubgroup_biInvariant K n b
  let L' : OpenSubgroup (FiniteAdelicGroupPoints K GLₙ) :=
    L.comap fH.toMulEquiv.toMonoidHom fH.continuous
  have hE (l : FiniteAdelicGroupPoints K GLₙ) : E (AdelicGroupPoints.ofFinite K GLₙ l) =
      AdelicGL.ofFinite K n (fH l) :=
    GeneralLinearGroupPoints.adelicHomeomorph_ofFinite K n l
  refine ⟨⟨hcont.comp E.continuous, ?_, L', L'.isOpen, ?_⟩, hcpt.comp_homeomorph E.toHomeomorph,
    L', L'.isOpen, ?_⟩
  · intro b'
    refine (GeneralLinearGroupPoints.isPlotSmooth_iff_mem_smoothFunctions K n _).mpr ?_
    have heq : (fun x => functionInfiniteSlice K GLₙ
        (fun g => adelicTestTensor K n a b (GeneralLinearGroupPoints.adelicHomeomorph K n g)) b'
          ((GeneralLinearGroupPoints.infiniteHomeomorph K n).symm x)) =
        b.val (fH b') • a.val.val := by
      funext x
      change ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n
          (E (AdelicGroupPoints.pair K GLₙ _ b'))) *
        b.val (AdelicGL.finite K n (E (AdelicGroupPoints.pair K GLₙ _ b'))) = _
      rw [GeneralLinearGroupPoints.adelicHomeomorph_pair, AdelicGL.infinite_pair,
        AdelicGL.finite_pair, ContinuousMulEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul,
        mul_comm]
      rfl
    rw [heq]
    exact Submodule.smul_mem _ _ a.val.property
  · intro l hl g
    change adelicTestTensor K n a b (E (g * AdelicGroupPoints.ofFinite K GLₙ l)) =
      adelicTestTensor K n a b (E g)
    rw [map_mul E, hE, (adelicTestTensor_ofFinite_mul K n a b (fH l) (E g)).2,
      (hL (fH l) hl _).2]
    rfl
  · intro l hl g
    change adelicTestTensor K n a b (E (AdelicGroupPoints.ofFinite K GLₙ l * g)) =
      adelicTestTensor K n a b (E g)
    rw [map_mul E, hE, (adelicTestTensor_ofFinite_mul K n a b (fH l) (E g)).1,
      (hL (fH l) hl _).1]
    rfl

set_option maxHeartbeats 1600000 in
/-- **Hilbert–Schmidt cuspidal operators of tensor tests in positive rank.** For `0 < n`, the
cuspidal integrated action of the tensor `a ⊗ b` on the full cuspidal subspace of `L²` of the
positive rational quotient of `GL_n` is Hilbert–Schmidt. -/
theorem generalLinearTensorCuspidalHilbertSchmidt_of_pos (hn : 0 < n)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant]
    (a : ArchimedeanGL.SmoothCompactKernel K n) (b : CompactFiniteGLTest K n)
    (h : Integrable (fun g => adelicTestTensor K n a b
      (GeneralLinearGroupPoints.adelicHomeomorph K n g))
      (Measure.haar : Measure (AdelicGroupPoints K GLₙ))) :
    IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T i hi I e hc Measure.haar
      (fun g => adelicTestTensor K n a b (GeneralLinearGroupPoints.adelicHomeomorph K n g)) h) :=
  (groupSchemeCuspidalConvolutionCompact T i hi I e hc hG
    (GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of K)) hPD hn
    (generalLinearStandard_isClosedSubgroup K n) _ h
    (isAdelicTestFunction_adelicTestTensor K n a b)).1

end Langlands.TraceFormula
