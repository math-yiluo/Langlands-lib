import Langlands.Global.Factors.CuspidalPairPoleEqualTestFamily
import Langlands.Global.RankinSelberg.OrdinaryLocalGrowthTransfer

/-! # An actual equal-rank normalized test with strip growth -/

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
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassFieldTheory.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem range_ne_bot {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {A : Type*} {M : V →ₗ[ℂ] (A → ℂ)} (a : A) (h : ∃ b, M b a = 1) : LinearMap.range M ≠ ⊥ := by
  obtain ⟨b, hb⟩ := h
  intro hM
  have hm := LinearMap.mem_range_self M b
  rw [hM, Submodule.mem_bot] at hm
  exact zero_ne_one ((congrFun hm a).symm.trans hb)

private theorem real_pair_invariant {r : ℕ} {d e : List RealBlock} {a : ℝˣ}
    {W W' : GeneralLinear (r + 1) ℝ → ℂ}
    (hW : W ∈ realWhittakerModel r d a) (hW' : W' ∈ realWhittakerModel r e (-a))
    (u : GeneralLinear.upperUnipotent (r + 1) ℝ) (g : GeneralLinear (r + 1) ℝ) :
    W (u.val * g) * W' (u.val * g) = W g * W' g := by
  have hL := (RealLocalWhittaker.model_le_regularFunctions d a hW).1
  have hR := (RealLocalWhittaker.model_le_regularFunctions e (-a) hW').1
  rw [hL _ u.property, hR _ u.property, mul_mul_mul_comm,
    RealEqualConvergence.realWhittakerCharacter_mul_neg, one_mul]

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {c : FinitePairLChoice P P' hP hP'} {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance poleEqualGrowthSchemeAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleEqualGrowthSchemeSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance poleEqualGrowthRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualGrowthContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualGrowthFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualGrowthAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance poleEqualGrowthStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- A standard-outside test with a nonzero normalized value at `s₀` and exponential strip growth. -/
def HasGrowthNormalizedEqualTestAt (c : FinitePairLChoice P P' hP hP')
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) (s₀ : ℂ) : Prop :=
  ∃ i : NormalizedEqualPoleTest c S ψ Linf,
    i.2.value s₀ ≠ 0 ∧ HasStripExponentialGrowth i.2.value

/-- Choose an actual ordinary equal-rank normalized test nonzero at the indicated point.
Local growth and the product formula give strip growth of its normalized function. -/
theorem exists_growthNormalizedEqualTest_of_local_at
    (c : FinitePairLChoice P P' hP hP')
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ν : ∀ v : S, LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v))
    (hGReal : Nonempty RP → RealOrdinaryNormalizedGenerationStatement) (hGComplex : ComplexOrdinaryNormalizedGenerationStatement)
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (aR : RP → ℝˣ) (aC : CP → ℂˣ)
    (dR dR' : RP → List RealBlock) (dC dC' : CP → List ComplexCharacterData)
    (hR : HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC)
    (hR' : HasSpecifiedWhittakerSliceRanges (P := P') (ψ := inverseCharacter ψ)
      M' (fun v => -aR v) (fun w => -aC w) dR' dC')
    (hdR : ∀ v, T.realization.HasRealPlaceParameter v (dR v))
    (hdR' : ∀ v, T'.realization.HasRealPlaceParameter v (dR' v))
    (hdC : ∀ w, T.realization.HasComplexPlaceParameter w (dC w))
    (hdC' : ∀ w, T'.realization.HasComplexPlaceParameter w (dC' w))
    (hGrowR : ∀ v, HasOrdinaryNormalizationStripGrowth
      (realOrdinaryEqualTest r (dR v) (dR' v) (aR v) (realQuotientMeasureData r)) (realPairLFactor (dR v) (dR' v)))
    (hGrowC : ∀ w, HasOrdinaryNormalizationStripGrowth
      (complexOrdinaryEqualTest r (dC w) (dC' w) (aC w) (complexQuotientMeasureData r))
      (complexPairLFactor (dC w) (dC' w))) (s₀ : ℂ) :
    HasGrowthNormalizedEqualTestAt c S ψ (archimedeanPairProduct dR dR' dC dC') s₀ := by
  have hFinite (v : S) := exists_poleFiniteEqualTest v.1 (ψv v) c (ν v) rfl hT hT' s₀
  choose D ΦS NS hNS using hFinite
  have hgR (v : RP) := ((hGReal ⟨v⟩).2 r (dR v) (dR' v) (hdR v).1 (hdR' v).1
    (T.isIrreducibleRealStandard v _ (hdR v)) (T'.isIrreducibleRealStandard v _ (hdR' v))
    (aR v) (realQuotientMeasureData r)
    (hR.1 v ▸ range_ne_bot 1 (M.normalized (.inl v)))
    (hR'.1 v ▸ range_ne_bot 1 (M'.normalized (.inl v)))).1 s₀
  have hgC (w : CP) := (hGComplex.2 r (dC w) (dC' w) (hdC w).1 (hdC' w).1
    (T.isIrreducibleComplexStandard w _ (hdC w)) (T'.isIrreducibleComplexStandard w _ (hdC' w))
    (aC w) (complexQuotientMeasureData r)
    (hR.2 w ▸ range_ne_bot 1 (M.normalized (.inr w)))
    (hR'.2 w ▸ range_ne_bot 1 (M'.normalized (.inr w)))).1 s₀
  choose R NR hNR using hgR
  choose C NC hNC using hgC
  let WR (v : RP) := (R v).1.val
  let WR' (v : RP) := (R v).2.1.val
  let WC (w : CP) := (C w).1.val
  let WC' (w : CP) := (C w).2.1.val
  have hWR (v : RP) : WR v ∈ LinearMap.range (M.model (.inl v)) := hR.1 v ▸ (R v).1.property
  have hWC (w : CP) : WC w ∈ LinearMap.range (M.model (.inr w)) := hR.2 w ▸ (C w).1.property
  have hWR' (v : RP) : WR' v ∈ LinearMap.range (M'.model (.inl v)) := hR'.1 v ▸ (R v).2.1.property
  have hWC' (w : CP) : WC' w ∈ LinearMap.range (M'.model (.inr w)) := hR'.2 w ▸ (C w).2.1.property
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
  let ΦR (v : RP) := (R v).2.2
  let ΦC (w : CP) := (C w).2.2
  have hN := exists_ordinaryEqualNormalization_of_pure_product (c := c) (hPS := hPS) (hPS' := hPS')
    hψF hψv D b b' WR WR' WC WC' ΦR ΦC ΦS (fun _ => realQuotientMeasureData r)
    (fun _ => complexQuotientMeasureData r) _ _ hProd.choose_spec.choose_spec.1 hProd'.choose_spec.choose_spec.1
    (fun v => real_pair_invariant (R v).1.property (R v).2.1.property)
    (fun w => ComplexCharacterChange.model_pair_invariant (C w).1.property (C w).2.1.property)
    hInf hInf' NR NC NS
  let x := P.allPlaceTensorEquiv hP (P.finitePure S hPS (fun v => (D v).leftFactor.vector) ⊗ₜ[ℂ] b)
  let x' := P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' (fun v => (D v).rightFactor.vector) ⊗ₜ[ℂ] b')
  let Φ := poleEqualSchwartzTensor ΦR ΦC ΦS
  have hΦ := poleEqualSchwartzTensor_spec ΦR ΦC ΦS
  let N := hN.choose_spec.2.choose
  have hvalue := hN.choose_spec.2.choose_spec s₀
  let test : EqualPoleTest T T' S := ⟨x, x', Φ,
    P.allPlaceTensorEquiv_finitePure_sphericalOutside hP S hPS _ b,
    P'.allPlaceTensorEquiv_finitePure_sphericalOutside hP' S hPS' _ b', hΦ.1, hΦ.2⟩
  refine ⟨⟨test, N⟩, ?_, ?_⟩
  · change N.value s₀ ≠ 0
    rw [hvalue]
    exact mul_ne_zero hN.choose_spec.1 (mul_ne_zero
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hNR v)
        (Finset.prod_ne_zero_iff.mpr fun w _ => hNC w))
      (Finset.prod_ne_zero_iff.mpr fun v _ => (hNS v).1))
  · change HasStripExponentialGrowth N.value
    have hGrow := stripGrowth_of_local_normalized_products (fun v => (NR v).value)
      (fun w => (NC w).value) (fun v => (NS v).value) hN.choose
      (fun v => hGrowR v (R v) (NR v)) (fun w => hGrowC w (C w) (NC w))
      (fun v => stripGrowth_of_norm_bounded_on_strips (hNS v).2)
    exact (funext hN.choose_spec.2.choose_spec).symm ▸ hGrow


theorem exists_growthNormalizedEqualTest_of_local
    (c : FinitePairLChoice P P' hP hP')
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ν : ∀ v : S, LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v))
    (hGReal : RealOrdinaryNormalizedGenerationStatement) (hGComplex : ComplexOrdinaryNormalizedGenerationStatement)
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (aR : RP → ℝˣ) (aC : CP → ℂˣ)
    (dR dR' : RP → List RealBlock) (dC dC' : CP → List ComplexCharacterData)
    (hR : HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC)
    (hR' : HasSpecifiedWhittakerSliceRanges (P := P') (ψ := inverseCharacter ψ)
      M' (fun v => -aR v) (fun w => -aC w) dR' dC')
    (hdR : ∀ v, T.realization.HasRealPlaceParameter v (dR v))
    (hdR' : ∀ v, T'.realization.HasRealPlaceParameter v (dR' v))
    (hdC : ∀ w, T.realization.HasComplexPlaceParameter w (dC w))
    (hdC' : ∀ w, T'.realization.HasComplexPlaceParameter w (dC' w))
    (hGrowR : ∀ v, HasOrdinaryNormalizationStripGrowth
      (realOrdinaryEqualTest r (dR v) (dR' v) (aR v) (realQuotientMeasureData r)) (realPairLFactor (dR v) (dR' v)))
    (hGrowC : ∀ w, HasOrdinaryNormalizationStripGrowth
      (complexOrdinaryEqualTest r (dC w) (dC' w) (aC w) (complexQuotientMeasureData r))
      (complexPairLFactor (dC w) (dC' w))) (s₀ : ℂ) :
    HasGrowthNormalizedEqualTestAt c S ψ (archimedeanPairProduct dR dR' dC dC') s₀ :=
  exists_growthNormalizedEqualTest_of_local_at c hPS hPS' hT hT' hψF hS hψv ν
    (fun _ => hGReal) hGComplex M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC' hGrowR hGrowC s₀

end Langlands.Global.CuspidalPairPoles
