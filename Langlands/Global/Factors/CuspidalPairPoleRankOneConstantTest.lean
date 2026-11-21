import Langlands.Global.Factors.CuspidalPairPoleEqualNormalizedProduct
import Langlands.Global.Factors.CuspidalPairPoleRankOneRanges
import Langlands.Global.Factors.CuspidalPairPoleEqualAssembly
import Langlands.Global.Factors.CuspidalPairPoleArchimedeanProduct
import Langlands.Representation.RankinSelberg.PadicRankOneOrdinaryTest

/-! A single global ordinary rank-one test with nonzero constant normalization. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField Set
open scoped Classical TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelberg RankinSelbergGlobal ArchimedeanLocal
open LocalFactor.Archimedean
open InfiniteWhittakerSlice FiniteWhittakerDual FiniteWhittakerSemilocal FiniteWhittakerTensor
open EqualSchwartzTensor
open CuspidalPairFunctionalEquation
open FunctionalEquationComparison.CompletedEquationAdapter
open ClassField.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)
open MeasureTheory QuotientIntegration Whittaker EqualFiniteWhittakerTests FiniteWhittakerModel

attribute [local instance 100] LieRing.ofAssociativeRing

local instance (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {T T' : CuspidalOperatorRealization F 0}
  {P : CuspidalSpectralPresentation.{u,uQ} T} {P' : CuspidalSpectralPresentation.{u,uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {S : Finset (FinitePlace F)} {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

private def constantOneNormalization {I L : ℂ → ℂ}
    (h : ∃ b : ℝ, ∀ s : ℂ, b < s.re → I s = L s) : OrdinaryIntegralNormalization I L :=
  ⟨fun _ => 1, analyticOnNhd_const, by
    obtain ⟨b, hb⟩ := h
    exact ⟨b, fun s hs => by rw [one_mul]; exact hb s hs⟩⟩

section Padic

variable (v : FinitePlace F) (χ : Correspondence.NontrivialAdditiveCharacter (padicField v))

local instance : TopologicalSpace (padicField v).Carrier := (padicField v).canonicalTopologicalData.topology
local instance : MeasurableSpace (padicField v).Carrier := borel _
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n (padicField v).Carrier) := borel _
local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance {n : ℕ} (A : LocalRealization F n v) : AddCommGroup A.Space := Submodule.addCommGroup _

private theorem exists_rankOnePoleFiniteTest (c : FinitePairLChoice P P' hP hP')
    (ν : LocalFactor.PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData χ)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T') :
    ∃ D : PoleFiniteTestVectors v χ P P', ∃ Φ : finiteRowTest F 1 v,
      ∃ N : OrdinaryIntegralNormalization (poleEqualFiniteIntegral v χ D Φ) (c.finiteL v),
        ∀ s, N.value s = 1 := by
  have hL := (isPadicSymmetricLPolynomial_of_le (le_refl 0)).mp (c.isIntegralPolynomialAt v χ ν hT hT')
  have ha := (P.localComponent v).isAdmissible_canonical_iff.mpr (hP v).2
  have ha' := (P'.localComponent v).isAdmissible_canonical_iff.mpr (hP' v).2
  obtain ⟨left, hleft, right, hright, Φ, b, hInt⟩ := padicRankOneOrdinaryTest (padicField v)
    χ ν.val _ _ (c.lPolynomial v) ha (hP v).1 ha' (hP' v).1 hL
  have hne (hz : left = 0 ∨ right = 0) : False := by
    have hP0 : (c.lPolynomial v).eval 0 ≠ 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, hL.coeff_zero]
      exact one_ne_zero
    obtain ⟨a, ha⟩ := exists_rightHalfPlane_eval_spectralPoint_ne_zero
      (padicField v).canonicalTopologicalData.residueCardinality_gt_one
      hP0
    let s : ℂ := ((max a b + 1 : ℝ) : ℂ)
    have hra : a < s.re := (le_max_left a b).trans_lt (by simp [s])
    have hrb : b < s.re := (le_max_right a b).trans_lt (by simp [s])
    have hzero := congrFun (equalRankIntegral_eq_zero
      (abv := normalizedAbsoluteValue (padicField v).canonicalTopologicalData)
      (equalPadicQuotientMeasure (padicField v) 0) hz Φ) s
    exact inv_ne_zero (ha s hra) (((hInt s hrb).2).symm.trans hzero)
  obtain ⟨ℓ, x, rfl⟩ := hleft
  obtain ⟨ℓ', x', rfl⟩ := hright
  have hℓ : ℓ.val ≠ 0 := by
    intro hz
    apply hne
    left
    apply Subtype.ext
    funext g
    change ℓ.val _ = 0
    rw [hz, LinearMap.zero_apply]
  have hℓ' : ℓ'.val ≠ 0 := by
    intro hz
    apply hne
    right
    apply Subtype.ext
    funext g
    change ℓ'.val _ = 0
    rw [hz, LinearMap.zero_apply]
  let ℓi : ComponentFunctionals P' v (inverseFinite v χ) :=
    functionalsCongr (inverse_factorCharacter (r := 0) v χ).symm ℓ'
  let D := factorCoefficient P v χ ℓ hℓ (modelMap (P.localComponent v).representation ℓ x)
  let D' := factorCoefficient P' v (inverseFinite v χ) ℓi hℓ'
    (modelMap (P'.localComponent v).representation ℓi x')
  exact ⟨⟨_, _, D, D'⟩, Φ, constantOneNormalization ⟨b, fun s hs => (hInt s hs).2⟩,
    fun _ => rfl⟩

end Padic

private theorem exists_realRankOneUnitTest {d d' : List RealBlock} {a : ℝˣ}
    (hd : realRank d = 1) (hd' : realRank d' = 1)
    {W W' : GeneralLinear 1 ℝ → ℂ} (hW : W ∈ realWhittakerModel 0 d a)
    (hW' : W' ∈ realWhittakerModel 0 d' (-a)) (h1 : W 1 = 1) (h1' : W' 1 = 1) :
    ∃ Φ : SchwartzMap (Fin 1 → ℝ) ℂ,
      ∃ N : OrdinaryIntegralNormalization (realEqualIntegral (realQuotientMeasureData 0) W W' Φ)
        (fun s => ((realPairLFactor d d').denominator s)⁻¹), ∀ s, N.value s = 1 := by
  obtain ⟨e, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hd
  obtain ⟨e', rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hd'
  obtain ⟨C, hC⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel hW
  obtain ⟨C', hC'⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel hW'
  have hC₀ : C ≠ 0 := by
    intro hz
    rw [hC 1, hz, zero_mul] at h1
    exact zero_ne_one h1
  have hC₀' : C' ≠ 0 := by
    intro hz
    rw [hC' 1, hz, zero_mul] at h1'
    exact zero_ne_one h1'
  obtain ⟨Φ, hΦ⟩ := RealRankZero.exists_realEqualIntegral_eq_LFactor (realQuotientMeasureData 0)
    e e' hC hC' hC₀ hC₀'
  refine ⟨Φ, constantOneNormalization ⟨-(e.mul e').exponent.re, fun s hs => hΦ s ?_⟩, fun _ => rfl⟩
  rw [Complex.add_re]
  linarith

private theorem exists_complexRankOneUnitTest {d d' : List ComplexCharacterData} {a : ℂˣ}
    (hd : d.length = 1) (hd' : d'.length = 1)
    {W W' : GeneralLinear 1 ℂ → ℂ} (hW : W ∈ complexWhittakerModel 0 d a)
    (hW' : W' ∈ complexWhittakerModel 0 d' (-a)) (h1 : W 1 = 1) (h1' : W' 1 = 1) :
    ∃ Φ : SchwartzMap (Fin 1 → ℂ) ℂ,
      ∃ N : OrdinaryIntegralNormalization (complexEqualIntegral (complexQuotientMeasureData 0) W W' Φ)
        (fun s => ((complexPairLFactor d d').denominator s)⁻¹), ∀ s, N.value s = 1 := by
  obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp hd
  obtain ⟨e', rfl⟩ := List.length_eq_one_iff.mp hd'
  obtain ⟨C, hC⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hW
  obtain ⟨C', hC'⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hW'
  have hC₀ : C ≠ 0 := by
    intro hz
    rw [hC 1, hz, zero_mul] at h1
    exact zero_ne_one h1
  have hC₀' : C' ≠ 0 := by
    intro hz
    rw [hC' 1, hz, zero_mul] at h1'
    exact zero_ne_one h1'
  obtain ⟨Φ, hΦ⟩ := ComplexRankZero.exists_complexEqualIntegral_eq_LFactor (complexQuotientMeasureData 0)
    e e' hC hC' hC₀ hC₀'
  refine ⟨Φ, constantOneNormalization ⟨-(e.mul e').exponent.re, fun s hs => hΦ s ?_⟩, fun _ => rfl⟩
  rw [Complex.add_re]
  linarith

/-- An actual standard-outside equal-rank test whose partial integral has a
nonzero constant entire normalization. -/
def HasRankOneConstantNormalizedTest (c : FinitePairLChoice P P' hP hP')
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) : Prop :=
  ∃ i : EqualPoleTest T T' S, ∃ C : ℂ, C ≠ 0 ∧
    ∃ N : OrdinaryIntegralNormalization
      (partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex i.left)
        (cuspWhittaker F T' ψ.complex⁻¹ i.right) i.schwartz)
      (fun s => Linf s * ∏ v ∈ S, c.finiteL v s), ∀ s, N.value s = C

/-- Normalizing tests at all places give a constant normalization for a single
actual pure tensor test. -/
theorem hasRankOneConstantNormalizedTest_of_ranges
    (c : FinitePairLChoice P P' hP hP') (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (aR : (RP F) → ℝˣ) (aC : (CP F) → ℂˣ)
    (dR dR' : (RP F) → List RealBlock) (dC dC' : (CP F) → List ComplexCharacterData)
    (hR : HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC)
    (hR' : HasSpecifiedWhittakerSliceRanges (P := P') (ψ := inverseCharacter ψ)
      M' (fun v => -aR v) (fun w => -aC w) dR' dC')
    (hdR : ∀ v, realRank (dR v) = 1) (hdR' : ∀ v, realRank (dR' v) = 1)
    (hdC : ∀ w, (dC w).length = 1) (hdC' : ∀ w, (dC' w).length = 1) :
    HasRankOneConstantNormalizedTest c S ψ (archimedeanPairProduct dR dR' dC dC') := by
  let ψv (v : S) := canonicalFiniteAdditiveComponent ψ hψF v.1
  have hψv (v : S) := isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hψF v.1
  let ν (v : S) : LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v) :=
    ⟨Correspondence.localSelfDualHaar (padicField v.1) (ψv v),
      Correspondence.isSelfDual_localSelfDualHaar (padicField v.1) (ψv v)⟩
  choose D ΦS NS hNS using fun (v : S) => exists_rankOnePoleFiniteTest v.1 (ψv v) c (ν v) hT hT'
  choose bR hbR using fun (v : (RP F)) => M.normalized (.inl v)
  choose bR' hbR' using fun (v : (RP F)) => M'.normalized (.inl v)
  choose bC hbC using fun (w : (CP F)) => M.normalized (.inr w)
  choose bC' hbC' using fun (w : (CP F)) => M'.normalized (.inr w)
  let WR (v : (RP F)) := M.model (.inl v) (bR v)
  let WR' (v : (RP F)) := M'.model (.inl v) (bR' v)
  let WC (w : (CP F)) := M.model (.inr w) (bC w)
  let WC' (w : (CP F)) := M'.model (.inr w) (bC' w)
  have hWR (v : (RP F)) := LinearMap.mem_range_self (M.model (.inl v)) (bR v)
  have hWR' (v : (RP F)) := LinearMap.mem_range_self (M'.model (.inl v)) (bR' v)
  have hWC (w : (CP F)) := LinearMap.mem_range_self (M.model (.inr w)) (bC w)
  have hWC' (w : (CP F)) := LinearMap.mem_range_self (M'.model (.inr w)) (bC' w)
  have hUnitR (v : (RP F)) := exists_realRankOneUnitTest (hdR v) (hdR' v)
    (hR.1 v ▸ hWR v) (hR'.1 v ▸ hWR' v) (hbR v) (hbR' v)
  have hUnitC (w : (CP F)) := exists_complexRankOneUnitTest (hdC w) (hdC' w)
    (hR.2 w ▸ hWC w) (hR'.2 w ▸ hWC' w) (hbC w) (hbC' w)
  choose ΦR NR hNR using hUnitR
  choose ΦC NC hNC using hUnitC
  have hProd := exists_prescribed_infiniteResidual_product
    (P := P) (hP := hP) (hPS := hPS) (ψ := ψ) (S := S) hψF hS ψv hψv
    (fun v => (D v).leftFactor.functional) (fun v => (D v).leftFactor.reference)
    (fun v => (D v).leftFactor.reference_value) M WR WC hWR hWC
  let ψ' := inverseCharacter ψ
  have hψ' (x : F) : ψ' (algebraMap F (Adeles F) x) = 1 := by
    change inverseCharacter ψ _ = 1
    rw [inverseCharacter_apply, hψF, inv_one]
  have hProd' := exists_prescribed_infiniteResidual_product
    (P := P') (hP := hP') (hPS := hPS') (ψ := ψ') (S := S) hψ'
    (finiteAdditiveSupport_inverseCharacter ψ S hS) (fun v => inverseFinite v.1 (ψv v))
    (fun v => canonical_inverse ψ v.1 (ψv v) (hψv v))
    (fun v => (D v).rightFactor.functional) (fun v => (D v).rightFactor.reference)
    (fun v => (D v).rightFactor.reference_value) M' WR' WC' hWR' hWC'
  let b := PiTensorProduct.tprod ℂ hProd.choose
  let b' := PiTensorProduct.tprod ℂ hProd'.choose
  have hInf := hProd.choose_spec.choose_spec.2
  have hInf' := hProd'.choose_spec.choose_spec.2
  simp only [ψ', complex_inverseCharacter] at hInf'
  have hN := exists_ordinaryEqualNormalization_of_pure_product (c := c) (hPS := hPS) (hPS' := hPS')
    hψF hψv D b b' WR WR' WC WC' ΦR ΦC ΦS (fun _ => realQuotientMeasureData 0)
    (fun _ => complexQuotientMeasureData 0) _ _ hProd.choose_spec.choose_spec.1 hProd'.choose_spec.choose_spec.1
    (fun _ z _ => by
      have hz : z = 1 := @Subsingleton.elim _ (upperUnipotent_one_subsingleton (F := ℝ)) _ _
      rw [hz, Subgroup.coe_one, one_mul])
    (fun _ z _ => by
      have hz : z = 1 := @Subsingleton.elim _ (upperUnipotent_one_subsingleton (F := ℂ)) _ _
      rw [hz, Subgroup.coe_one, one_mul])
    hInf hInf' NR NC NS
  let x := P.allPlaceTensorEquiv hP (P.finitePure S hPS (fun v => (D v).leftFactor.vector) ⊗ₜ[ℂ] b)
  let x' := P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' (fun v => (D v).rightFactor.vector) ⊗ₜ[ℂ] b')
  let Φ := poleEqualSchwartzTensor ΦR ΦC ΦS
  have hΦ := poleEqualSchwartzTensor_spec ΦR ΦC ΦS
  obtain ⟨C, hC, N, hN⟩ := hN
  refine ⟨⟨x, x', Φ, P.allPlaceTensorEquiv_finitePure_sphericalOutside hP S hPS _ b,
    P'.allPlaceTensorEquiv_finitePure_sphericalOutside hP' S hPS' _ b', hΦ.1, hΦ.2⟩,
    C, hC, N, fun s => ?_⟩
  rw [hN s]
  simp [hNR, hNC, hNS]

/-- Every actual rank-one pair with the prescribed archimedean parameters has a
single test of nonzero constant normalization at each sufficiently large finite set. -/
def RankOneConstantNormalizedTestStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (T T' : CuspidalOperatorRealization F 0),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (hP : HasIrreducibleAdmissibleComponents P) (hP' : HasIrreducibleAdmissibleComponents P')
    (c : FinitePairLChoice P P' hP hP') (S : Finset (FinitePlace F)),
    P.exceptional ⊆ S → P'.exceptional ⊆ S → FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (dR dR' : (RP F) → List RealBlock) (dC dC' : (CP F) → List ComplexCharacterData),
    (∀ v, T.realization.HasRealPlaceParameter v (dR v)) →
    (∀ v, T'.realization.HasRealPlaceParameter v (dR' v)) →
    (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
    (∀ w, T'.realization.HasComplexPlaceParameter w (dC' w)) →
    HasRankOneConstantNormalizedTest c S ψ (archimedeanPairProduct dR dR' dC dC')

/-- Obtain the rank-one slice models on the supplied actual presentations and
assemble the constant-normalization test. -/
theorem rankOneConstantNormalizedTest : RankOneConstantNormalizedTestStatement.{u,uQ} := by
  intro F _ _ _ ψ hψ T T' hT hT' P P' hP hP' c S hPS hPS' hS dR dR' dC dC' hdR hdR' hdC hdC'
  choose aR haR using fun v => exists_isRealAdditiveComponent ψ hψ v
  choose aC haC using fun w => exists_isComplexAdditiveComponent ψ hψ w
  obtain ⟨M, _, hR, _⟩ := rankOneSpecifiedWhittakerSliceComparisonAt ψ hψ T hT P hP
    aR haR aC haC dR hdR dC hdC
  obtain ⟨_, M', _, hR'⟩ := rankOneSpecifiedWhittakerSliceComparisonAt ψ hψ T' hT' P' hP'
    aR haR aC haC dR' hdR' dC' hdC'
  exact hasRankOneConstantNormalizedTest_of_ranges c hPS hPS' hT hT' hψ hS M M' aR aC
    dR dR' dC dC' hR hR' (fun v => (hdR v).1) (fun v => (hdR' v).1)
    (fun w => (hdC w).1) (fun w => (hdC' w).1)

end Langlands.Global.CuspidalPairPoles
