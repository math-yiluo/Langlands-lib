import Langlands.Global.RankinSelberg.ComplexAdjacentSplitIntegrals
import Langlands.Global.RankinSelberg.ComplexSquareConvolutionGeneration
import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedContinuationProof
import Langlands.Global.RankinSelberg.OrdinaryNormalizationLinear

/-! # Ordinary adjacent normalization through square convolution -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.LocalFactor

section LinearTrace

variable {V X : Type*} [AddCommGroup V] [Module ℂ V] [MeasurableSpace X]

/-- Integrating a polynomial family in a convergent linear family uses one common right
half-plane for the identities of all its coefficient vectors. -/
theorem integral_polynomialFamily_eq_on_right (μ : Measure X) (L : ℂ → ℂ)
    (K : V →ₗ[ℂ] (ℂ → X → ℂ)) (A : V →ₗ[ℂ] (ℂ → ℂ))
    (hA : ∀ v, ∃ N : OrdinaryIntegralNormalization (fun s => ∫ x, K v s x ∂μ) L, A v = N.value)
    (hI : ∀ v, ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (K v s) μ)
    {F : ℂ → V} (hF : ∃ (l : ℕ) (p : Fin l → Polynomial ℂ) (v : Fin l → V),
      ∀ s, F s = ∑ j, (p j).eval s • v j) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re → (∫ x, K (F s) s x ∂μ) = A (F s) s * L s := by
  obtain ⟨l, p, v, hv⟩ := hF
  choose N hN using fun j => hA (v j)
  choose b hB using fun j => (N j).eq_on_right
  choose c hC using fun j => hI (v j)
  obtain ⟨τ, hτ⟩ := (finite_range fun j => max (b j) (c j)).bddAbove
  refine ⟨τ, fun s hs => ?_⟩
  have hτ' (j : Fin l) : max (b j) (c j) < s.re := (hτ (mem_range_self j)).trans_lt hs
  simp only [hv s, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum]
  · simp only [integral_const_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hB j s ((le_max_left _ _).trans_lt (hτ' j)), hN j, mul_assoc]
  · exact fun j _ => (hC j s ((le_max_right _ _).trans_lt (hτ' j))).const_mul _

end LinearTrace

namespace ComplexAdjacentUnfolding

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open ComplexGodement (characterWeight normPower)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementColumnProduct (columnProduct)
open ComplexJacquet (HasSquareConvolutionTrace complexLocalEqualEndpointConvergence
  complexJacquetMatrixIntegrand square_detPower_eq_normPower)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => (r + 1 : ℕ)
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear (m + 1) ℂ
local notation "Mat" => Matrix (Fin m) (Fin m) ℂ
local notation "Row" => Fin m → ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "KF[" es "]" => complexStandardKFinite m es
local notation "gap" => Nat.lt_succ_self r

/-- Values of a Whittaker intertwiner as vectors in the corresponding Whittaker model. -/
def whittakerVector {es : List ComplexCharacterData} {a : ℂˣ} {B : KF[es] →ₗ[ℂ] (H → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r es a B) (v : KF[es]) : complexWhittakerModel r es a :=
  ⟨B v, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)⟩

@[simp] theorem whittakerVector_val {es : List ComplexCharacterData} {a : ℂˣ}
    {B : KF[es] →ₗ[ℂ] (H → ℂ)} (hB : IsComplexWhittakerIntertwiner r es a B) (v : KF[es]) :
    (whittakerVector hB v).val = B v := rfl

/-- The equal-rank quotient integrand is linear in the opposite coefficient. -/
def equalIntegrandLinear (U : H → ℂ) (ψ : Row → ℂ) : (H → ℂ) →ₗ[ℂ] (ℂ → Q → ℂ) where
  toFun V := complexEqualIntegrand U V ψ
  map_add' V W := by
    funext s q
    simp only [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, Pi.add_apply]
    ring
  map_smul' c V := by
    funext s q
    simp only [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- At fixed equal-rank data the entire normalized values depend linearly on the opposite
inducing vector in any prescribed Whittaker realization. -/
theorem exists_complexEqualNormalizationLinear (D : ComplexQuotientMeasureData r) (a : ℂˣ)
    (ds es : List ComplexCharacterData) (hd : ds.length = m) (he : es.length = m)
    (U : complexWhittakerModel r ds (-a)) (ψ : 𝓢(Row, ℂ))
    (B : KF[es] →ₗ[ℂ] (H → ℂ)) (hB : IsComplexWhittakerIntertwiner r es a B) :
    ∃ A : KF[es] →ₗ[ℂ] (ℂ → ℂ), ∀ v,
      ∃ N : OrdinaryIntegralNormalization (complexEqualIntegral D U.val (B v) ψ)
        (fun s => ((complexPairLFactor ds es).denominator s)⁻¹), A v = N.value := by
  classical
  let K := (equalIntegrandLinear U.val ψ).comp B
  let L s := ((complexPairLFactor ds es).denominator s)⁻¹
  have hV (v : KF[es]) : B v ∈ complexWhittakerModel r es (-(-a)) := by
    simpa only [neg_neg, whittakerVector_val] using (whittakerVector hB v).2
  have hI (v : KF[es]) : ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (K v s) D.measure := by
    obtain ⟨b, hb⟩ := complexLocalEqualEndpointConvergence hd he (-a) D U.val (B v) ψ U.2 (hV v)
    exact ⟨b, fun s hs => (hb s hs).1⟩
  obtain ⟨b, hb⟩ := complexPairLFactor_denominator_ne_zero ds es
  let N (v : KF[es]) : OrdinaryIntegralNormalization (fun s => ∫ q, K v s q ∂D.measure) L :=
    Classical.choice (complexOrdinaryNormalizedContinuation.2 r ds es hd he (-a) D (U, ⟨B v, hV v⟩, ψ))
  obtain ⟨A, hA⟩ := ordinaryNormalizationLinear D.measure K L ⟨b, fun s hs => inv_ne_zero (hb s hs)⟩ hI N
  exact ⟨A, fun v => ⟨N v, hA v⟩⟩

private theorem cons_pairFactor (d : ComplexCharacterData) (ds es : List ComplexCharacterData) :
    complexPairLFactor (d :: ds) es = (complexPairLFactor [d] es).mul (complexPairLFactor ds es) := by
  simp only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    complexLFactor_append]

/-- The adjacent split integral normalizes to the lower equal-rank normalized integral
applied to the normalized square convolution vector, times the Weyl phase. -/
def ComplexAdjacentSquareTraceStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure] (a : ℂˣ) (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (e : Fin m → ComplexCharacterData), ds.length = m →
    ∀ (U : complexWhittakerModel r ds (-a)) (B : KF[List.ofFn e] →ₗ[ℂ] (H → ℂ)),
      IsComplexWhittakerIntertwiner r (List.ofFn e) a B →
    ∀ (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Row, ℂ)) (f : KF[List.ofFn e]) (F : ℂ → KF[List.ofFn e]),
      HasSquareConvolutionTrace D.groupHaar d e B Φ f F →
    ∀ A : KF[List.ofFn e] →ₗ[ℂ] (ℂ → ℂ),
      (∀ v, ∃ N : OrdinaryIntegralNormalization (complexEqualIntegral D U.val (B v) (splitRowTransform a φ))
        (fun s => ((complexPairLFactor ds (List.ofFn e)).denominator s)⁻¹), A v = N.value) →
    let W (g : G) := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (columnProduct Φ φ)) U.val g 0
    ∃ N : OrdinaryIntegralNormalization (complexUnequalIntegral gap D W (B f))
        (fun s => ((complexPairLFactor (d :: ds) (List.ofFn e)).denominator s)⁻¹),
      ∀ s, N.value s = (d.character ((-1 : ℂˣ) ^ m) : ℂ) * A (F s) s

set_option maxHeartbeats 1200000 in
theorem complexAdjacentSquareTrace : ComplexAdjacentSquareTraceStatement (r := r) := by
  intro D hD a d ds e hd U B hB Φ φ f F hF A hA W
  let e₀ := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := e₀.locallyCompactSpace
  let : SecondCountableTopology H := e₀.secondCountableTopology
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : SFinite μ := inferInstance
  let es := List.ofFn e
  let ψ := splitRowTransform a φ
  let c : ℂ := d.character ((-1 : ℂˣ) ^ m)
  let L (s : ℂ) := (complexPairLFactor [d] es).denominator s
  let K := (equalIntegrandLinear U.val ψ).comp B
  let R (s : ℂ) := c * A (F s) s
  have hR : Differentiable ℂ R := by
    obtain ⟨l, p, v, hv⟩ := hF.1
    have hA' (j : Fin l) : Differentiable ℂ (A (v j)) := by
      obtain ⟨N, hN⟩ := hA (v j)
      rw [hN]
      exact fun s => (N.analytic s (mem_univ _)).differentiableAt
    dsimp only [R]
    simp_rw [hv, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (Differentiable.fun_sum fun j _ => (p j).differentiable.mul (hA' j)).const_mul c
  have hV (v : KF[es]) : B v ∈ complexWhittakerModel r es (-(-a)) := by
    simpa only [neg_neg, whittakerVector_val] using (whittakerVector hB v).2
  have hI (v : KF[es]) : ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (K v s) D.measure := by
    obtain ⟨b, hb⟩ := complexLocalEqualEndpointConvergence hd List.length_ofFn (-a) D U.val (B v) ψ U.2 (hV v)
    exact ⟨b, fun s hs => (hb s hs).1⟩
  obtain ⟨bA, hbA⟩ := integral_polynomialFamily_eq_on_right D.measure _ K A hA hI hF.1
  obtain ⟨bL, hbL⟩ := complexPairLFactor_denominator_ne_zero [d] es
  obtain ⟨bF, hbF⟩ := hF.2
  obtain ⟨bZ, hbZ⟩ := complexAdjacentSplitIntegrals D a d 0 Φ φ ds es hd List.length_ofFn U (whittakerVector hB f)
  let b := max (max bA bL) (max bF bZ)
  refine ⟨⟨R, fun s _ => hR.analyticAt s, b, fun s hs => ?_⟩, fun _ => rfl⟩
  have h₁ := (le_max_left (max bA bL) (max bF bZ)).trans_lt hs
  have h₂ := (le_max_right (max bA bL) (max bF bZ)).trans_lt hs
  have hne : L s ≠ 0 := hbL s ((le_max_right bA bL).trans_lt h₁)
  have hFₛ := hbF s ((le_max_left bF bZ).trans_lt h₂)
  have hZ := hbZ s ((le_max_right bF bZ).trans_lt h₂)
  let J (q : Q) (g : H) := complexJacquetMatrixIntegrand d (fun g => B f (q.out * g)) Φ s g
  let E (q : Q) := U.val q.out * ψ (Langlands.RankinSelberg.lastRow q.out) *
    ArchimedeanLocal.detPower complexNormalizedAbs q.out s
  let I := unfoldedKernel d (0 + (r : ℂ) / 2) s Φ ψ U.val (B f)
  have hKer (g : H) (q : Q) : I (g, q) = E q * J q g := by
    simp only [I, E, J, unfoldedKernel, ArchimedeanLocal.equalIntegrand, complexJacquetMatrixIntegrand,
      square_detPower_eq_normPower, zero_add, add_comm ((r : ℂ) / 2) s]
    change Φ g.val * ((d.character (determinant g) : ℂ) * normPower _ (determinant g)) * _ = _
    ring
  have hInner (q : Q) : (∫ g, J q g ∂μ) = (L s)⁻¹ * B (F s) q.out := by
    rw [hFₛ q.out]
    change _ = (L s)⁻¹ * (L s * ∫ g, J q g ∂μ)
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hOuter (q : Q) : E q * ((L s)⁻¹ * B (F s) q.out) = (L s)⁻¹ * K (F s) s q := by
    change _ = _ * (U.val q.out * B (F s) q.out * ψ (Langlands.RankinSelberg.lastRow q.out) *
      ArchimedeanLocal.detPower complexNormalizedAbs q.out s)
    dsimp only [E]
    ring
  have hEach (q : Q) : (∫ g, I (g, q) ∂μ) = (L s)⁻¹ * K (F s) s q := by
    simp_rw [hKer]
    rw [integral_const_mul, hInner, hOuter]
  change complexUnequalIntegral gap D W (B f) s = R s * _
  have hZeq : complexUnequalIntegral gap D W (B f) s = c * ∫ y, I y ∂μ.prod D.measure := hZ.2.2.1
  have hProd : (∫ y, I y ∂μ.prod D.measure) = ∫ q, ∫ g, I (g, q) ∂μ ∂D.measure :=
    integral_prod_symm I hZ.1
  rw [hZeq, hProd]
  simp_rw [hEach, integral_const_mul]
  rw [hbA s ((le_max_left bA bL).trans_lt h₁), cons_pairFactor, ReciprocalEntire.denominator_mul, mul_inv]
  change c * ((L s)⁻¹ * (A (F s) s * ((complexPairLFactor ds es).denominator s)⁻¹)) = _
  dsimp only [R, L]
  ring

end ComplexAdjacentUnfolding
end Langlands.Global.RankinSelbergGlobal
