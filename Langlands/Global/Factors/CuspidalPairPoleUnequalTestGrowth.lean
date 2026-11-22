import Langlands.Global.Factors.CuspidalPairPoleUnequalLocalTests
import Langlands.Global.Factors.CuspidalPairPoleArchimedeanProduct
import Langlands.Global.RankinSelberg.OrdinaryLocalGrowthTransfer
import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof

/-! # Covering unequal-rank normalized tests with strip growth -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000

universe u uQ

open scoped Classical TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open NumberField Automorphic CompletionPadic RankinSelberg RankinSelbergGlobal
open RankinSelbergGlobal.FiniteWhittakerPartialDomain
open RankinSelbergGlobal.FiniteWhittakerSemilocal
open RankinSelbergGlobal.UnequalIntegrandProducts
open LocalPointFactorization
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassField.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)
open MeasureTheory ArchimedeanLocal LocalFactor.Archimedean
open InfiniteWhittakerSlice FiniteWhittakerDual FiniteWhittakerTensor

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] ArchimedeanLocal.archimedeanRealQMeasurable
  ArchimedeanLocal.archimedeanRealQBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanRealGLMeasurable
  ArchimedeanLocal.archimedeanRealGLBorel ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanRealNMeasurable
  ArchimedeanLocal.archimedeanRealNBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)}

local instance poleUnequalGrowthSchemeAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleUnequalGrowthSchemeSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance poleUnequalGrowthRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance poleUnequalGrowthContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance poleUnequalGrowthFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance poleUnequalGrowthAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance poleUnequalGrowthStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

private theorem realUnequal_pair_invariant {r t : ℕ} (h : t < r) {d e : List RealBlock} {a : ℝˣ}
    {W : GeneralLinear (r + 1) ℝ → ℂ} {W' : GeneralLinear (t + 1) ℝ → ℂ}
    (hW : W ∈ realWhittakerModel r d a) (hW' : W' ∈ realWhittakerModel t e (-a))
    (u : GeneralLinear.upperUnipotent (t + 1) ℝ) (g : GeneralLinear (t + 1) ℝ) :
    let hp := Nat.succ_le_succ h.le
    W (padGL hp (u.val * g)) * W' (u.val * g) = W (padGL hp g) * W' g := by
  intro hp
  have hL := (RealLocalWhittaker.model_le_regularFunctions d a hW).1
  have hR := (RealLocalWhittaker.model_le_regularFunctions e (-a) hW').1
  rw [map_mul, hL _ (RealUnequalConvergence.padGL_mem_upperUnipotent hp u.property),
    hR _ u.property, RealUnequalConvergence.realWhittakerCharacter_padGL h hp,
    mul_mul_mul_comm, RealEqualConvergence.realWhittakerCharacter_mul_neg, one_mul]

private theorem complexUnequal_pair_invariant {r t : ℕ} (h : t < r) {d e : List ComplexCharacterData} {a : ℂˣ}
    {W : GeneralLinear (r + 1) ℂ → ℂ} {W' : GeneralLinear (t + 1) ℂ → ℂ}
    (hW : W ∈ complexWhittakerModel r d a) (hW' : W' ∈ complexWhittakerModel t e (-a))
    (u : GeneralLinear.upperUnipotent (t + 1) ℂ) (g : GeneralLinear (t + 1) ℂ) :
    let hp := Nat.succ_le_succ h.le
    W (padGL hp (u.val * g)) * W' (u.val * g) = W (padGL hp g) * W' g := by
  intro hp
  have hq : (Quotient.mk'' g : LeftUnipotentQuotient t ℂ) = Quotient.mk'' (u.val * g) :=
    (LeftCosetSpace.mk_eq_mk_iff _ _ _).mpr (by simp [mul_assoc])
  let s : ℂ := ((r - t : ℕ) : ℂ) / 2
  have he := congrArg (complexUnequalIntegrand h W W' s) hq.symm
  rw [complexUnequalIntegrand_mk h hW hW', complexUnequalIntegrand_mk h hW hW'] at he
  simpa [s, ArchimedeanLocal.detPower] using he

private theorem range_ne_bot_of_normalized {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {A : Type*} {B : V →ₗ[ℂ] (A → ℂ)} (a : A) (h : ∃ b, B b a = 1) : LinearMap.range B ≠ ⊥ := by
  obtain ⟨b, hb⟩ := h
  intro hB
  have hm : B b ∈ LinearMap.range B := LinearMap.mem_range_self B b
  rw [hB, Submodule.mem_bot] at hm
  exact zero_ne_one ((congrFun hm a).symm.trans hb)

private theorem mul_products {I J : Type*} [Fintype I] [Fintype J] (κ κ' : ℂ)
    (f f' : I → ℂ) (g g' : J → ℂ) :
    (κ * ((∏ i, f i) * ∏ j, g j)) * (κ' * ((∏ i, f' i) * ∏ j, g' j)) =
      κ * κ' * ((∏ i, f i * f' i) * ∏ j, g j * g' j) := by
  simp only [Finset.prod_mul_distrib]
  ac_rfl

section Padic

variable (v : FinitePlace F)
local instance poleUnequalGrowthPadicTopology : TopologicalSpace (padicField v).Carrier := (padicField v).canonicalTopologicalData.topology
local instance poleUnequalGrowthPadicValuation : ValuativeRel (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.valuativeRel
local instance poleUnequalGrowthPadicLocalField : IsNonarchimedeanLocalField (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.localField
local instance poleUnequalGrowthPadicMeasurable : MeasurableSpace (padicField v).Carrier := borel (padicField v).Carrier
local instance poleUnequalGrowthPadicBorel : BorelSpace (padicField v).Carrier := ⟨rfl⟩
local instance poleUnequalGrowthPadicQuotientMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n (padicField v).Carrier) := borel _

/-- The ordinary finite integral for an exact local test of an unequal-rank pair. -/
def poleUnequalFiniteIntegral {k : ℕ} (hr : r = t + (0 + k + 1))
    (χ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : LocalFactor.PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData χ)
    (D : PoleFiniteTestVectors v χ P P') : ℂ → ℂ :=
  unequalRankIntegralAt 0 k hr χ (normalizedAbsoluteValue (padicField v).canonicalTopologicalData)
    (equalPadicQuotientMeasure (padicField v) t) (rectangularMeasure ν.val 0 (t + 1)) D.left D.right

private theorem padicIntegral_eq_blockZero {k : ℕ} (hr : r = t + (0 + k + 1)) (hrt : t < r)
    (χ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : LocalFactor.PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData χ)
    (D : PoleFiniteTestVectors v χ P P') (s : ℂ) :
    padicQuotientIntegral (padicField v) (equalPadicQuotientMeasure (padicField v) t)
      (ArchimedeanLocal.unequalIntegrand
        (normalizedAbsoluteValue (padicField v).canonicalTopologicalData) hrt D.left.val D.right.val s) =
      unequalRankIntegralAt 0 k hr χ (normalizedAbsoluteValue (padicField v).canonicalTopologicalData)
        (equalPadicQuotientMeasure (padicField v) t) (rectangularMeasure ν.val 0 (t + 1)) D.left D.right s :=
  unequalIntegral_eq_blockZero hr hrt χ _ _ ν.val D.left D.right s

end Padic

variable {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}

/-- An ordinary test tuple at the infinite and specified finite places realizes its
product of normalized values up to a nonzero scalar. -/
theorem exists_normalizedUnequalPureTest_of_prescribed
    (c : FinitePairLChoice P P' hP hP') (hrt : t < r) {k : ℕ} (hr : r = t + (0 + k + 1))
    (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ν : ∀ v : S, LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v))
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (aR : RP → ℝˣ) (aC : CP → ℂˣ)
    (dR dR' : RP → List RealBlock) (dC dC' : CP → List ComplexCharacterData)
    (hR : HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC)
    (hR' : HasSpecifiedWhittakerSliceRanges (P := P') (ψ := inverseCharacter ψ)
      M' (fun v => -aR v) (fun w => -aC w) dR' dC')
    (R : ∀ v : RP, realWhittakerModel r (dR v) (aR v) × realWhittakerModel t (dR' v) (-aR v))
    (C : ∀ w : CP, complexWhittakerModel r (dC w) (aC w) × complexWhittakerModel t (dC' w) (-aC w))
    (NR : ∀ v, OrdinaryIntegralNormalization
      (realOrdinaryUnequalTest hrt (dR v) (dR' v) (aR v) (realQuotientMeasureData t) (R v))
      (fun s => ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹))
    (NC : ∀ w, OrdinaryIntegralNormalization
      (complexOrdinaryUnequalTest hrt (dC w) (dC' w) (aC w) (complexQuotientMeasureData t) (C w))
      (fun s => ((complexPairLFactor (dC w) (dC' w)).denominator s)⁻¹))
    (D : ∀ v : S, PoleFiniteTestVectors v.1 (ψv v) P P')
    (NS : ∀ v : S, OrdinaryIntegralNormalization
      (poleUnequalFiniteIntegral v.1 hr (ψv v) (ν v) (D v)) (c.finiteL v.1)) :
    ∃ (x : T.Space) (x' : T'.Space), IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S x' ∧
      ∃ N : OrdinaryIntegralNormalization
        (partialUnequalWhittakerIntegral F hrt S (cuspWhittaker F T ψ.complex x)
          (cuspWhittaker F T' ψ.complex⁻¹ x'))
        (fun s => archimedeanPairProduct dR dR' dC dC' s * ∏ v ∈ S, c.finiteL v s),
        ∃ K : ℂ, K ≠ 0 ∧ ∀ s, N.value s = K *
          (((∏ v, (NR v).value s) * ∏ w, (NC w).value s) * ∏ v : S, (NS v).value s) := by
  let LR (v : RP) (s : ℂ) := ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹
  let LC (w : CP) (s : ℂ) := ((complexPairLFactor (dC w) (dC' w)).denominator s)⁻¹
  let WR (v : RP) := (R v).1.val
  let WR' (v : RP) := (R v).2.val
  let WC (w : CP) := (C w).1.val
  let WC' (w : CP) := (C w).2.val
  have hWR (v : RP) : (R v).1.val ∈ LinearMap.range (M.model (.inl v)) := by
    rw [hR.1 v]
    exact (R v).1.property
  have hWC (w : CP) : (C w).1.val ∈ LinearMap.range (M.model (.inr w)) := by
    rw [hR.2 w]
    exact (C w).1.property
  have hWR' (v : RP) : (R v).2.val ∈ LinearMap.range (M'.model (.inl v)) := by
    rw [hR'.1 v]
    exact (R v).2.property
  have hWC' (w : CP) : (C w).2.val ∈ LinearMap.range (M'.model (.inr w)) := by
    rw [hR'.2 w]
    exact (C w).2.property
  let ℓ (v : S) : FactorFunctionals P v.1 (ψv v) := (D v).leftFactor.functional
  let a₀ (v : S) : P.localFactor v := (D v).leftFactor.reference
  have ha₀ (v : S) : (ℓ v).val (a₀ v) = 1 := (D v).leftFactor.reference_value
  have hProd := exists_prescribed_infiniteResidual_product
    (P := P) (hP := hP) (hPS := hPS) (ψ := ψ) (S := S)
    hψF hS ψv hψv ℓ a₀ ha₀ M WR WC hWR hWC
  let b := hProd.choose
  let κ := hProd.choose_spec.choose
  have hκ := hProd.choose_spec.choose_spec.1
  have hb := hProd.choose_spec.choose_spec.2
  let ψ' := inverseCharacter ψ
  let ψv' (v : S) := inverseFinite v.1 (ψv v)
  have hψ' (x : F) : ψ' (algebraMap F (Adeles F) x) = 1 := by
    change inverseCharacter ψ _ = 1
    rw [inverseCharacter_apply, hψF, inv_one]
  let ℓ' (v : S) : FactorFunctionals P' v.1 (ψv' v) := (D v).rightFactor.functional
  let a₀' (v : S) : P'.localFactor v := (D v).rightFactor.reference
  have ha₀' (v : S) : (ℓ' v).val (a₀' v) = 1 := (D v).rightFactor.reference_value
  have hProd' := exists_prescribed_infiniteResidual_product
    (P := P') (hP := hP') (hPS := hPS') (ψ := ψ') (S := S)
    hψ' (finiteAdditiveSupport_inverseCharacter ψ S hS) ψv'
    (fun v => canonical_inverse ψ v.1 (ψv v) (hψv v)) ℓ' a₀' ha₀' M' WR' WC' hWR' hWC'
  let b' := hProd'.choose
  let κ' := hProd'.choose_spec.choose
  have hκ' := hProd'.choose_spec.choose_spec.1
  have hb' := hProd'.choose_spec.choose_spec.2
  let bInf := PiTensorProduct.tprod ℂ b
  let bInf' := PiTensorProduct.tprod ℂ b'
  let hp := Nat.succ_le_succ hrt.le
  let U := cuspWhittaker F T ψ.complex (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] bInf))
  let U' := cuspWhittaker F T' ψ.complex⁻¹ (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a₀' ⊗ₜ[ℂ] bInf'))
  have hArch (g : Points F (t + 1)) :
      U (pad F hp (infinitePoint S g)) * U' (infinitePoint S g) = (κ * κ') *
        ((∏ v, WR v (padGL hp (realComponent F (t + 1) v g)) *
          WR' v (realComponent F (t + 1) v g)) *
          ∏ w, WC w (padGL hp (complexComponent F (t + 1) w g)) *
            WC' w (complexComponent F (t + 1) w g)) := by
    have hl := hb (pad F hp g)
    have hr' := hb' g
    simp only [infiniteResidual] at hl hr'
    simp only [realComponent_pad, complexComponent_pad] at hl
    have hl' : U (pad F hp (infinitePoint S g)) = κ *
        ((∏ v, WR v (padGL hp (realComponent F (t + 1) v g))) *
          ∏ w, WC w (padGL hp (complexComponent F (t + 1) w g))) :=
      (congrArg U (pad_infinitePoint hp S g)).trans hl
    have hr'' : U' (infinitePoint S g) = κ' *
        ((∏ v, WR' v (realComponent F (t + 1) v g)) *
          ∏ w, WC' w (complexComponent F (t + 1) w g)) := by
      simpa only [ψ', complex_inverseCharacter] using hr'
    exact (congrArg₂ (· * ·) hl' hr'').trans (mul_products κ κ' _ _ _ _)
  let a (v : S) := (D v).leftFactor.vector
  let a' (v : S) := (D v).rightFactor.vector
  let x := P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] bInf)
  let x' := P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] bInf')
  let W := cuspWhittaker F T ψ.complex x
  let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
  have hf := hasOrdinaryUnequalFiniteProduct hrt hP hP' hPS hPS' ψ hψF hψv D bInf bInf'
  dsimp only [HasOrdinaryUnequalFiniteProduct] at hf
  have hW (g : Points F (t + 1)) (hg : g ∈ unipotentIntegralOutside F (t + 1) S) :
      W (pad F hp g) * W' g = (κ * κ') *
        ((∏ v, WR v (padGL hp (realComponent F (t + 1) v g)) * WR' v (realComponent F (t + 1) v g)) *
        (∏ w, WC w (padGL hp (complexComponent F (t + 1) w g)) * WC' w (complexComponent F (t + 1) w g)) *
        ∏ v : S, (D v).left.val (padGL hp (finiteComponent F (t + 1) v.1 g)) *
          (D v).right.val (finiteComponent F (t + 1) v.1 g)) :=
    (hf g hg).trans ((congrArg (fun z : ℂ => z * _) (hArch g)).trans (mul_assoc _ _ _))
  have hpoint := pairedWhittakerIntegrandProduct F hrt S (κ * κ') W W'
    WR WR' WC WC'
    (fun v => (D v).left.val) (fun v => (D v).right.val)
    (fun v => realUnequal_pair_invariant hrt (R v).1.property (R v).2.property) (fun w => complexUnequal_pair_invariant hrt (C w).1.property (C w).2.property)
    (fun v => by
      let _ : TopologicalSpace (padicField v.1).Carrier := (padicField v.1).canonicalTopologicalData.topology
      exact unequalPair_invariant hr (ψv v) (D v).left (D v).right hrt) hW
  let fS (v : S) := ArchimedeanLocal.unequalIntegrand
    (normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData) hrt (D v).left.val (D v).right.val
  let NS' (v : S) : OrdinaryIntegralNormalization
      (fun s => padicQuotientIntegral (padicField v.1) (equalPadicQuotientMeasure (padicField v.1) t) (fS v s))
      (c.finiteL v.1) :=
    ⟨(NS v).value, (NS v).analytic, by
      obtain ⟨b, hb⟩ := (NS v).eq_on_right
      exact ⟨b, fun s hs => (padicIntegral_eq_blockZero v.1 hr hrt (ψv v) (ν v) (D v) s).trans (hb s hs)⟩⟩
  obtain ⟨K, hK, N, hN⟩ := exists_normalization_of_semilocal_pointwise_product
    (fun _ => realQuotientMeasureData t) (fun _ => complexQuotientMeasureData t) (fun v => equalPadicQuotientMeasure (padicField v.1) t)
    (fun v => equalPadicQuotientMeasure_isCompatible (padicField v.1) t)
    (unequalWhittakerIntegrand F hrt W W') (mul_ne_zero hκ hκ')
    (fun v => ArchimedeanLocal.realUnequalIntegrand hrt (WR v) (WR' v))
    (fun w => ArchimedeanLocal.complexUnequalIntegrand hrt (WC w) (WC' w))
    fS ⟨0, fun s _ q hq => hpoint s q hq⟩ NR NC NS'
  refine ⟨x, x', P.allPlaceTensorEquiv_finitePure_sphericalOutside hP S hPS a bInf,
    P'.allPlaceTensorEquiv_finitePure_sphericalOutside hP' S hPS' a' bInf',
    ⟨N.value, N.analytic, ?_⟩, K, hK, hN⟩
  obtain ⟨b, hb⟩ := N.eq_on_right
  refine ⟨b, fun s hs => ?_⟩
  rw [partialUnequalWhittakerIntegral_eq_setIntegral, hb s hs]
  exact congrArg (fun a : ℂ => N.value s * (((∏ v, LR v s) * ∏ w, LC w s) * a))
    (Finset.prod_coe_sort S (fun v => c.finiteL v s))

/-- An actual ordinary unequal-rank family that covers every spectral point and contains a
nonzero normalized member having exponential strip growth. -/
def HasCoveringUnequalNormalizedGrowthTests (c : FinitePairLChoice P P' hP hP')
    (hrt : t < r) (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) : Prop :=
  ∃ D : UnequalNormalizedTests.{u, uQ, u} c hrt S ψ Linf,
    ∃ i, (∃ z, D.normalized i z ≠ 0) ∧ HasStripExponentialGrowth (D.normalized i)

/-- Realize the local normalized unequal tests at the indicated parameters and multiply
the local growth estimates using the actual normalized partial integral formula. -/
theorem hasCoveringUnequalNormalizedGrowthTests_of_local_at
    (c : FinitePairLChoice P P' hP hP') (hrt : t < r)
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
      (realOrdinaryUnequalTest hrt (dR v) (dR' v) (aR v) (realQuotientMeasureData t)) (realPairLFactor (dR v) (dR' v)))
    (hGrowC : ∀ w, HasOrdinaryNormalizationStripGrowth
      (complexOrdinaryUnequalTest hrt (dC w) (dC' w) (aC w) (complexQuotientMeasureData t))
      (complexPairLFactor (dC w) (dC' w))) :
    HasCoveringUnequalNormalizedGrowthTests c hrt S ψ (archimedeanPairProduct dR dR' dC dC') := by
  let LR (v : RP) (s : ℂ) := ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹
  let LC (w : CP) (s : ℂ) := ((complexPairLFactor (dC w) (dC' w)).denominator s)⁻¹
  have hOne (s₀ : ℂ) : ∃ (x : T.Space) (x' : T'.Space),
      IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S x' ∧
      ∃ N : OrdinaryIntegralNormalization
        (partialUnequalWhittakerIntegral F hrt S (cuspWhittaker F T ψ.complex x)
          (cuspWhittaker F T' ψ.complex⁻¹ x'))
        (fun s => ((∏ v, LR v s) * ∏ w, LC w s) * ∏ v ∈ S, c.finiteL v s),
        N.value s₀ ≠ 0 ∧ HasStripExponentialGrowth N.value := by
    let k := r - (t + 1)
    have hr : r = t + (0 + k + 1) := by dsimp [k]; omega
    choose D NS hNS using fun v : S => exists_poleFiniteUnequalTest v.1 (ψv v) c (ν v) hr hT hT' s₀
    have hgR (v : RP) := ((hGReal ⟨v⟩).1 r t hrt (dR v) (dR' v) (hdR v).1 (hdR' v).1
      (T.isIrreducibleRealStandard v _ (hdR v)) (T'.isIrreducibleRealStandard v _ (hdR' v))
      (aR v) (realQuotientMeasureData t)
      (hR.1 v ▸ range_ne_bot_of_normalized 1 (M.normalized (.inl v)))
      (hR'.1 v ▸ range_ne_bot_of_normalized 1 (M'.normalized (.inl v)))).1 s₀
    have hgC (w : CP) := (hGComplex.1 r t hrt (dC w) (dC' w) (hdC w).1 (hdC' w).1
      (T.isIrreducibleComplexStandard w _ (hdC w)) (T'.isIrreducibleComplexStandard w _ (hdC' w))
      (aC w) (complexQuotientMeasureData t)
      (hR.2 w ▸ range_ne_bot_of_normalized 1 (M.normalized (.inr w)))
      (hR'.2 w ▸ range_ne_bot_of_normalized 1 (M'.normalized (.inr w)))).1 s₀
    choose R NR hNR using hgR
    choose C NC hNC using hgC
    obtain ⟨x, x', hx, hx', N, K, hK, hN⟩ :=
      exists_normalizedUnequalPureTest_of_prescribed c hrt hr hPS hPS' hψF hS hψv ν M M'
        aR aC dR dR' dC dC' hR hR' R C NR NC D NS
    refine ⟨x, x', hx, hx', N, ?_, ?_⟩
    · rw [hN]
      exact mul_ne_zero hK (mul_ne_zero
        (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hNR v)
          (Finset.prod_ne_zero_iff.mpr fun w _ => hNC w))
        (Finset.prod_ne_zero_iff.mpr fun v _ => (hNS v).1))
    · have hg := stripGrowth_of_local_normalized_products (fun v => (NR v).value)
        (fun w => (NC w).value) (fun v => (NS v).value) K
        (fun v => hGrowR v (R v) (NR v)) (fun w => hGrowC w (C w) (NC w))
        (fun v => stripGrowth_of_norm_bounded_on_strips (hNS v).2)
      exact (funext hN).symm ▸ hg
  choose x x' hx hx' N hN using hOne
  refine ⟨⟨ULift.{u} ℂ, fun i => x i.down, fun i => x' i.down, fun i => hx i.down, fun i => hx' i.down,
    fun i => (N i.down).value, fun i => (N i.down).analytic, fun s => ⟨ULift.up s, (hN s).1⟩,
    fun i => ?_⟩, ULift.up 0, ⟨0, (hN 0).1⟩, (hN 0).2⟩
  obtain ⟨b, hb⟩ := (N i.down).eq_on_right
  exact ⟨b, fun s hs => (hb s hs).trans (mul_assoc _ _ _).symm⟩


theorem hasCoveringUnequalNormalizedGrowthTests_of_local
    (c : FinitePairLChoice P P' hP hP') (hrt : t < r)
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
      (realOrdinaryUnequalTest hrt (dR v) (dR' v) (aR v) (realQuotientMeasureData t)) (realPairLFactor (dR v) (dR' v)))
    (hGrowC : ∀ w, HasOrdinaryNormalizationStripGrowth
      (complexOrdinaryUnequalTest hrt (dC w) (dC' w) (aC w) (complexQuotientMeasureData t))
      (complexPairLFactor (dC w) (dC' w))) :
    HasCoveringUnequalNormalizedGrowthTests c hrt S ψ (archimedeanPairProduct dR dR' dC dC') :=
  hasCoveringUnequalNormalizedGrowthTests_of_local_at c hrt hPS hPS' hT hT' hψF hS hψv ν
    (fun _ => hGReal) hGComplex M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC' hGrowR hGrowC

end Langlands.Global.CuspidalPairPoles
