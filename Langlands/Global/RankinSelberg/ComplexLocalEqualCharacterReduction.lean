import Langlands.Global.RankinSelberg.ComplexLocalEqualKernelChange
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction

/-! # The complex equal-rank local equation for a standard additive character -/

noncomputable section

open MeasureTheory
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.LocalFactor.Archimedean

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The complete analytic package for the local equal-rank equation, with additive
parameters `1` and `-1`. -/
def ComplexLocalEqualStandardCharacterStatement : Prop := by
  classical
  exact
    ∀ (r : ℕ) (d d' : List ComplexCharacterData), d.length = r + 1 → d'.length = r + 1 →
      ∀ (D : ComplexQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
        (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
        W ∈ complexWhittakerModel r d 1 → W' ∈ complexWhittakerModel r d' (-1) →
      ∃ (σ : ℝ) (M Md : ℂ → ℂ),
        (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
        (∀ s : ℂ, σ < s.re →
          Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
            (ArchimedeanLocal.dualFunction (r + 1) W') (complexFourierTransform 1 Φ) s)
            D.measure) ∧
        DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
        DifferentiableOn ℂ (complexEqualDualIntegral 1 D W W' Φ) {s : ℂ | σ < s.re} ∧
        MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
        (∀ s : ℂ, σ < s.re → complexEqualIntegral D W W' Φ s = M s) ∧
        (∀ s : ℂ, σ < s.re → complexEqualDualIntegral 1 D W W' Φ s = Md s) ∧
        ∀ᶠ s in Filter.codiscrete ℂ,
          ((complexPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
            complexCentralSign d' ^ r *
              (complexPairEpsilon d d' 1 ‖(↑(1 : ℂˣ) : ℂ)‖₊
                (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ) *
              ((complexPairLFactor (d.map ComplexCharacterData.inv)
                (d'.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹ * M s

/-- A standard-character reduction of the published local equation for all the
Library's nontrivial complex additive characters. -/
def ComplexLocalEqualCharacterReductionStatement : Prop :=
  ComplexLocalEqualStandardCharacterStatement → ComplexLocalEqualFunctionalEquationStatement

namespace ComplexCharacterChange

private theorem prod_character_block (x : ComplexCharacterData) (ys : List ComplexCharacterData)
    (a : ℂˣ) :
    ((ys.map x.mul).map fun d => (d.character a : ℂ)).prod =
      (x.character a : ℂ) ^ ys.length * (centralCharacter ys a : ℂ) := by
  rw [coe_centralCharacter]
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ih]
    change (x.character a : ℂ) * (y.character a : ℂ) *
        ((x.character a : ℂ) ^ ys.length * (ys.map fun d => (d.character a : ℂ)).prod) =
      _
    ring

private theorem prod_character_pairBlocks (ds ds' : List ComplexCharacterData) (a : ℂˣ) :
    ((complexPairBlocks ds ds').map fun d => (d.character a : ℂ)).prod =
      (centralCharacter ds a : ℂ) ^ ds'.length * (centralCharacter ds' a : ℂ) ^ ds.length := by
  induction ds with
  | nil => simp [complexPairBlocks, centralCharacter]
  | cons d ds ih =>
    rw [complexPairBlocks, List.flatMap_cons, ← complexPairBlocks, List.map_append, List.prod_append,
      prod_character_block, ih, List.length_cons, pow_succ]
    change _ = ((d.character a : ℂ) * (centralCharacter ds a : ℂ)) ^ ds'.length *
      ((centralCharacter ds' a : ℂ) ^ ds.length * (centralCharacter ds' a : ℂ))
    rw [mul_pow]
    ring

/-- The multipliers at the two arguments reproduce the change in the pair
epsilon factor, including the self-dual measure scale. -/
theorem epsilon_mul_primal_eq_dual_mul_standard {r : ℕ}
    {ds ds' : List ComplexCharacterData} (hlen : ds.length = r + 1) (hlen' : ds'.length = r + 1)
    (a : ℂˣ) (s : ℂ) :
    (complexPairEpsilon ds ds' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
        primalMultiplier r a s =
      dualMultiplier r ds ds' a (1 - s) *
        (complexPairEpsilon ds ds' 1 ‖(↑(1 : ℂˣ) : ℂ)‖₊
          (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ) := by
  let n := r + 1
  let k := n * n
  let χ := (centralCharacter ds a : ℂ) * (centralCharacter ds' a : ℂ)
  let phase := ((complexPairBlocks ds ds').map fun d => Complex.I ^ d.weight.natAbs).prod
  have hpow : (k : ℂ) + 2 * (k : ℂ) * (s - 1) + (-(r : ℂ) * (r + 1) * s) =
      (r + 1) - (r + 1) * (r + 2) * (1 - s) := by
    dsimp [k, n]
    push_cast
    ring
  simp only [complexPairEpsilon, coe_complexEpsilon, prod_character_pairBlocks,
    length_complexPairBlocks, hlen, hlen', map_one, Units.val_one, nnnorm_one, NNReal.coe_one,
    norm_one, Complex.ofReal_one, one_pow, Complex.one_cpow, List.prod_map_one, mul_one, one_mul, ← mul_pow,
    primalMultiplier, dualMultiplier]
  change ((‖(a : ℂ)‖ : ℂ) ^ k * χ ^ n *
      (‖(a : ℂ)‖ : ℂ) ^ (2 * (k : ℂ) * (s - 1)) * phase) *
      amplitude a (-(r : ℂ) * (r + 1) * s) =
    χ ^ n * amplitude a ((r + 1) - (r + 1) * (r + 2) * (1 - s)) * phase
  rw [← amplitude_natCast, ← amplitude_cpow]
  calc
    _ = χ ^ n * (amplitude a (k : ℂ) * amplitude a (2 * (k : ℂ) * (s - 1)) *
        amplitude a (-(r : ℂ) * (r + 1) * s)) * phase := by ring
    _ = _ := by rw [← amplitude_add, ← amplitude_add, hpow]

private theorem differentiable_amplitude (a : ℂˣ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun s => amplitude a (f s) :=
  (hf.mul_const _).cexp

theorem differentiable_primalMultiplier (r : ℕ) (a : ℂˣ) :
    Differentiable ℂ (primalMultiplier r a) :=
  differentiable_amplitude a (differentiable_id.const_mul _)

theorem differentiable_dualMultiplier (r : ℕ) (ds ds' : List ComplexCharacterData) (a : ℂˣ) :
    Differentiable ℂ (dualMultiplier r ds ds' a) := by
  unfold dualMultiplier
  exact (differentiable_amplitude a
    ((differentiable_const _).sub (differentiable_id.const_mul _))).const_mul _

end ComplexCharacterChange

open ComplexCharacterChange

/-- The standard-character equation gives the equation for arbitrary `a`, with all
analytic clauses transferred by the quotient changes of variables. -/
theorem complexLocalEqualCharacterReduction : ComplexLocalEqualCharacterReductionStatement := by
  classical
  intro h r ds ds' hlen hlen' a D W W' Φ hW hW'
  let V := normalizeWhittaker a W
  let V' := normalizeWhittaker a W'
  let D₁ := changeQuotientMeasure a D
  obtain ⟨σ, M, Md, hI, hId, hH, hHd, hM, hMd, hE, hEd, hFE⟩ :=
    h r ds ds' hlen hlen' D₁ V V' Φ (normalizeWhittaker_mem hW) (normalizeWhittaker_neg_mem hW')
  let c := primalMultiplier r a
  let cd := dualMultiplier r ds ds' a
  have hprimal : complexEqualIntegral D W W' Φ = fun s => c s * complexEqualIntegral D₁ V V' Φ s :=
    funext fun s => (primal_comparison hW hW' D Φ s).2
  have hdual : complexEqualDualIntegral a D W W' Φ =
      fun s => cd s * complexEqualDualIntegral 1 D₁ V V' Φ s :=
    funext fun s => (dual_comparison hlen hlen' hW hW' D Φ s).2
  have hc : Differentiable ℂ c := differentiable_primalMultiplier r a
  have hcd : Differentiable ℂ cd := differentiable_dualMultiplier r ds ds' a
  refine ⟨σ, fun s => c s * M s, fun s => cd s * Md s,
    fun s hs => (primal_comparison hW hW' D Φ s).1.mpr (hI s hs),
    fun s hs => (dual_comparison hlen hlen' hW hW' D Φ s).1.mpr (hId s hs),
    hprimal ▸ hc.differentiableOn.mul hH, hdual ▸ hcd.differentiableOn.mul hHd,
    (hc.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn.mul hM,
    (hcd.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn.mul hMd, ?_, ?_, ?_⟩
  · intro s hs
    rw [hprimal]
    exact congrArg (c s * ·) (hE s hs)
  · intro s hs
    rw [hdual]
    exact congrArg (cd s * ·) (hEd s hs)
  · filter_upwards [hFE] with s hs
    let e := (complexPairEpsilon ds ds' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)
    let e₁ := (complexPairEpsilon ds ds' 1 ‖(↑(1 : ℂˣ) : ℂ)‖₊
      (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ)
    let L := ((complexPairLFactor ds ds').denominator s)⁻¹
    let Ld := ((complexPairLFactor (ds.map ComplexCharacterData.inv)
      (ds'.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹
    let sign := complexCentralSign ds' ^ r
    change L * (cd (1 - s) * Md (1 - s)) = sign * e * Ld * (c s * M s)
    change L * Md (1 - s) = sign * e₁ * Ld * M s at hs
    have he : e * c s = cd (1 - s) * e₁ :=
      epsilon_mul_primal_eq_dual_mul_standard hlen hlen' a s
    calc
      _ = cd (1 - s) * (L * Md (1 - s)) := by ring
      _ = sign * (cd (1 - s) * e₁) * Ld * M s := by rw [hs]; ring
      _ = _ := by rw [← he]; ring

end Langlands.Global.RankinSelbergGlobal
