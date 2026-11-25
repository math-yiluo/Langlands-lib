import Langlands.Global.Factors.CuspidalPairPoleUnequalNormalizedProduct
import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.ArchimedeanQuotientMeasures
import Langlands.Global.RankinSelberg.InfiniteWhittakerPrescribedProduct
import Langlands.Global.RankinSelberg.RealUnequalConvergence
import Langlands.Global.RankinSelberg.ComplexLocalUnequalKernels

/-! # Unequal-rank archimedean coverage from local slice models -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

universe u uQ

open NumberField
open scoped Classical TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelbergGlobal ArchimedeanLocal
open LocalFactor.Archimedean
open RankinSelberg (LeftUnipotentQuotient)
open Langlands.Archimedean
open InfiniteWhittakerSlice FiniteWhittakerDual FiniteWhittakerSemilocal FiniteWhittakerTensor
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassFieldTheory.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

attribute [local instance 100] LieRing.ofAssociativeRing

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

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {S : Finset (FinitePlace F)} {hPS : P.exceptional ⊆ S} {hPS' : P'.exceptional ⊆ S}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {hrt : t < r}
  {ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

/-- The ranges of the one-place coefficient maps agree with the prescribed local
coefficient models for the indicated signs of the additive parameters. -/
def HasSpecifiedWhittakerSliceRanges (M : ModelData P hP ψ.complex)
    (aR : RP → ℝˣ) (aC : CP → ℂˣ) (dR : RP → List RealBlock) (dC : CP → List ComplexCharacterData) : Prop :=
  (∀ v, LinearMap.range (M.model (.inl v)) = realWhittakerModel r (dR v) (aR v)) ∧
  ∀ w, LinearMap.range (M.model (.inr w)) = complexWhittakerModel r (dC w) (aC w)

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

/-- Realize independently chosen normalized local pairs on the two actual infinite tensors. -/
theorem hasCoveringUnequalArchimedeanTests_of_slice_test_ranges
    {LR : RP → ℂ → ℂ} {LC : CP → ℂ → ℂ}
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (M : ModelData P hP ψ.complex) (M' : ModelData P' hP' (inverseCharacter ψ).complex)
    (hLocal : ∀ s₀, ∃ A : PoleUnequalArchimedeanTest hrt LR LC s₀,
      (∀ v, A.realLeft v ∈ LinearMap.range (M.model (.inl v))) ∧
      (∀ w, A.complexLeft w ∈ LinearMap.range (M.model (.inr w))) ∧
      (∀ v, A.realRight v ∈ LinearMap.range (M'.model (.inl v))) ∧
      (∀ w, A.complexRight w ∈ LinearMap.range (M'.model (.inr w)))) :
    HasCoveringUnequalArchimedeanTests (P := P) (P' := P') hP hP' hPS hPS' ψ hrt ψv LR LC := by
  intro D s₀
  let A := (hLocal s₀).choose
  have hA := (hLocal s₀).choose_spec
  let ℓ (v : S) : FactorFunctionals P v.1 (ψv v) := (D v).leftFactor.functional
  let a₀ (v : S) : P.localFactor v := (D v).leftFactor.reference
  have ha₀ (v : S) : (ℓ v).val (a₀ v) = 1 := (D v).leftFactor.reference_value
  have hProd := exists_prescribed_infiniteResidual_product
    (P := P) (hP := hP) (hPS := hPS) (ψ := ψ) (S := S)
    hψF hS ψv hψv ℓ a₀ ha₀ M A.realLeft A.complexLeft hA.1 hA.2.1
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
    (fun v => canonical_inverse ψ v.1 (ψv v) (hψv v)) ℓ' a₀' ha₀' M' A.realRight A.complexRight hA.2.2.1 hA.2.2.2
  let b' := hProd'.choose
  let κ' := hProd'.choose_spec.choose
  have hκ' := hProd'.choose_spec.choose_spec.1
  have hb' := hProd'.choose_spec.choose_spec.2
  refine ⟨PiTensorProduct.tprod ℂ b, PiTensorProduct.tprod ℂ b', A, κ * κ', mul_ne_zero hκ hκ', ?_⟩
  intro hp U U' g _
  have hleft := hb (pad F hp g)
  have hright := hb' g
  simp only [infiniteResidual] at hleft hright
  simp only [realComponent_pad, complexComponent_pad] at hleft
  have hleft' : U (pad F hp (infinitePoint S g)) = κ *
      ((∏ v, A.realLeft v (padGL hp (realComponent F (t + 1) v g))) *
        ∏ w, A.complexLeft w (padGL hp (complexComponent F (t + 1) w g))) :=
    (congrArg U (pad_infinitePoint hp S g)).trans hleft
  have hright' : U' (infinitePoint S g) = κ' *
      ((∏ v, A.realRight v (realComponent F (t + 1) v g)) *
        ∏ w, A.complexRight w (complexComponent F (t + 1) w g)) := hright
  exact (congrArg₂ (· * ·) hleft' hright').trans (mul_products κ κ' _ _ _ _)

/-- Given exact model ranges and pointwise local generation, choose compatible local
quotient measures and realize the required normalized unequal-rank products on cuspidal tensors.
Use real generation only when the field has a real place. -/
theorem hasCoveringUnequalArchimedeanTests_of_local_at
    (hGReal : Nonempty RP → RealOrdinaryNormalizedGenerationStatement)
    (hGComplex : ComplexOrdinaryNormalizedGenerationStatement)
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
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
    (hiR : ∀ v, IsIrreducibleGKModule (realStandardRep (r + 1) (dR v)) (realStandardLie (r + 1) (dR v)))
    (hiR' : ∀ v, IsIrreducibleGKModule (realStandardRep (t + 1) (dR' v)) (realStandardLie (t + 1) (dR' v)))
    (hiC : ∀ w, IsIrreducibleGKModule (complexStandardRep (r + 1) (dC w)) (complexStandardLie (r + 1) (dC w)))
    (hiC' : ∀ w, IsIrreducibleGKModule (complexStandardRep (t + 1) (dC' w)) (complexStandardLie (t + 1) (dC' w))) :
    HasCoveringUnequalArchimedeanTests (P := P) (P' := P') hP hP' hPS hPS' ψ hrt ψv
      (fun v s => ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹)
      (fun w s => ((complexPairLFactor (dC w) (dC' w)).denominator s)⁻¹) := by
  refine hasCoveringUnequalArchimedeanTests_of_slice_test_ranges hψF hS hψv M M' ?_
  intro s₀
  have hgR (v : RP) := ((hGReal ⟨v⟩).1 r t hrt (dR v) (dR' v) (hdR v).1 (hdR' v).1 (hiR v) (hiR' v)
    (aR v) (realQuotientMeasureData t)
    (hR.1 v ▸ range_ne_bot_of_normalized 1 (M.normalized (.inl v)))
    (hR'.1 v ▸ range_ne_bot_of_normalized 1 (M'.normalized (.inl v)))).1 s₀
  have hgC (w : CP) := (hGComplex.1 r t hrt (dC w) (dC' w) (hdC w).1 (hdC' w).1 (hiC w) (hiC' w)
    (aC w) (complexQuotientMeasureData t)
    (hR.2 w ▸ range_ne_bot_of_normalized 1 (M.normalized (.inr w)))
    (hR'.2 w ▸ range_ne_bot_of_normalized 1 (M'.normalized (.inr w)))).1 s₀
  choose R NR hNR using hgR
  choose C NC hNC using hgC
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
  let A : PoleUnequalArchimedeanTest hrt
      (fun v s => ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹)
      (fun w s => ((complexPairLFactor (dC w) (dC' w)).denominator s)⁻¹) s₀ :=
    ⟨fun v => (R v).1.val, fun v => (R v).2.val, fun w => (C w).1.val, fun w => (C w).2.val,
      fun _ => realQuotientMeasureData t, fun _ => complexQuotientMeasureData t, NR, NC,
      hNR, hNC, fun v => realUnequal_pair_invariant hrt (R v).1.property (R v).2.property,
      fun w => complexUnequal_pair_invariant hrt (C w).1.property (C w).2.property⟩
  exact ⟨A, hWR, hWC, hWR', hWC'⟩

theorem hasCoveringUnequalArchimedeanTests_of_local
    (hGReal : RealOrdinaryNormalizedGenerationStatement) (hGComplex : ComplexOrdinaryNormalizedGenerationStatement)
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
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
    (hiR : ∀ v, IsIrreducibleGKModule (realStandardRep (r + 1) (dR v)) (realStandardLie (r + 1) (dR v)))
    (hiR' : ∀ v, IsIrreducibleGKModule (realStandardRep (t + 1) (dR' v)) (realStandardLie (t + 1) (dR' v)))
    (hiC : ∀ w, IsIrreducibleGKModule (complexStandardRep (r + 1) (dC w)) (complexStandardLie (r + 1) (dC w)))
    (hiC' : ∀ w, IsIrreducibleGKModule (complexStandardRep (t + 1) (dC' w)) (complexStandardLie (t + 1) (dC' w))) :
    HasCoveringUnequalArchimedeanTests (P := P) (P' := P') hP hP' hPS hPS' ψ hrt ψv
      (fun v s => ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹)
      (fun w s => ((complexPairLFactor (dC w) (dC' w)).denominator s)⁻¹) :=
  hasCoveringUnequalArchimedeanTests_of_local_at (fun _ => hGReal) hGComplex
    hψF hS hψv M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC' hiR hiR' hiC hiC'

end Langlands.Global.CuspidalPairPoles
