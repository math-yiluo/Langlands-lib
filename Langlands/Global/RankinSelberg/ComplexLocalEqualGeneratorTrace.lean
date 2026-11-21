import Langlands.Analysis.Complex.AffineTraceRecovery
import Langlands.Global.RankinSelberg.ComplexLocalEqualChamberUnfolding
import Langlands.Global.RankinSelberg.ComplexLocalEqualNormalizedFactors
import Langlands.Global.RankinSelberg.ComplexLocalEqualGeneratorFamily
import Langlands.Global.RankinSelberg.ComplexPairParameterReflection

/-! # Recovery of the ordinary equal-rank traces from the normalized square transform -/

noncomputable section

open MeasureTheory Set
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (characterOfParams characterOfParams_exponent characterOfParams_weight)
open Langlands.GodementJacquet
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz OperatorSchwartz operatorToEntry)
open scoped NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open ArchimedeanLocal
open ComplexJacquet
open ComplexGodement (SmallerProfile HasFullRowRank smallerWeights smallerExponents addedCharacter
  characterList_cons shiftedCharacter shiftedCharacter_exponent)
open ComplexCompactProfileFamily (characterList standardSection standardSection_mem standardSection_unitary
  compactRestriction compactRestriction_isCompactProfile)
open ComplexAdjacentUnfolding (differentiable_pairDenominator differentiable_pairDualDenominator
  complexCentralSign_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => r + 1 + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "P" => Fin n → ℂ
local notation "L" => Fin n → ℤ
local notation "ud" => ArchimedeanLocal.dualFunction m
local notation "wd" => ArchimedeanLocal.dualFunction n

private theorem differentiable_adjoining (q : Fin m → ℂ) :
    Differentiable ℂ (fun z : ℂ => (Fin.cons (α := fun _ : Fin n => ℂ) z q : P)) := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact differentiable_id
  · exact differentiable_const (q j)

private theorem characterList_adjoining (l : L) (q : Fin m → ℂ) (z : ℂ) :
    characterList l (Fin.cons z q) =
      shiftedCharacter (characterOfParams (l 0) 0) z :: characterList (smallerWeights l) q := by
  rw [characterList_cons]
  simp only [addedCharacter, Fin.cons_zero, ComplexGodement.retainedCharacters, shiftedCharacter,
    characterOfParams_exponent, characterOfParams_weight, zero_add]
  rfl

/-- The canonical evaluation of a compact profile belongs to the exact Whittaker model. -/
theorem canonicalJacquetProfile_mem (a : ℂˣ) (l : L) (q : Fin m → ℂ) (f : SmallerProfile l) :
    canonicalJacquetFamily (complexSelfDualMeasure a) a (smallerWeights l) f.val f.2 q ∈
      complexWhittakerModel r (characterList (smallerWeights l) q) (-a) := by
  let B := continuedJacquet (complexSelfDualMeasure a) a (smallerWeights l) q
  let v : Automorphic.complexStandardKFinite m (characterList (smallerWeights l) q) :=
    ⟨standardSection q f.val, standardSection_mem f.2 q⟩
  have hv : B v = canonicalJacquetFamily (complexSelfDualMeasure a) a (smallerWeights l) f.val f.2 q := by
    have he : compactRestriction v.val = f.val := funext (standardSection_unitary q f.val)
    change canonicalJacquetFamily (complexSelfDualMeasure a) a (smallerWeights l)
      (compactRestriction v.val) (compactRestriction_isCompactProfile v.2) q = _
    congr
  rw [← hv]
  exact Submodule.mem_iSup_of_mem B
    (Submodule.mem_iSup_of_mem (complexJacquetCanonicalIntertwiner _ a _ q) ⟨v, rfl⟩)

private theorem sign_adjoining (d : ComplexCharacterData) (z : ℂ) :
    ((shiftedCharacter d z).character (-1) : ℂ) = (d.character (-1) : ℂ) := by
  rw [(shiftedCharacter d z).character_eq, d.character_eq]
  simp [shiftedCharacter, characterOfParams_weight]

private theorem inverse_shifted_character (d : ComplexCharacterData) (z : ℂ) :
    (shiftedCharacter d z).character.toMonoidHom.comp invMonoidHom =
      (shiftedCharacter d.inv (-z)).character.toMonoidHom := by
  rw [← shiftedCharacter_inv_eq]
  ext w
  simp [ComplexCharacterData.inv_character_apply]

private theorem stripGrowth_const_mul {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) (c : ℂ) :
    HasStripExponentialGrowth (fun s => c * f s) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, h⟩ := hf a b
  refine ⟨‖c‖ * C, K, T, mul_nonneg (norm_nonneg _) hC, hK, fun s hs ht hT => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h s hs ht hT) (norm_nonneg _)

private theorem stripGrowth_reflect {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) :
    HasStripExponentialGrowth (fun s => f (1 - s)) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, h⟩ := hf (1 - b) (1 - a)
  refine ⟨C, K, T, hC, hK, fun s hs ht hT => ?_⟩
  have him : |(1 - s).im| = |s.im| := by simp [Complex.sub_im]
  rw [← him]
  apply h (1 - s) _ _ (him ▸ hT)
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
  · simp only [Complex.sub_re, Complex.one_re]
    linarith

/-- An entire square-test continuation with the two chamber traces is sufficient
for the entire normalized equation of each compact rectangular recursion generator. -/
def ComplexLocalEqualGeneratorTraceStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (l l' : L) (q : Fin m → ℂ) (p' : P) (Φ : OperatorSchwartz m n),
    HasCompactSupport Φ → (∀ X ∈ tsupport Φ, HasFullRowRank X) →
    ∀ (f : SmallerProfile l) (f' : Automorphic.complexStandardKFinite n (characterList l' p'))
      (φ : 𝓢(Row, ℂ)),
    let μ := complexSelfDualMeasure 1
    let d := characterOfParams (l 0) 0
    let ds := characterList (smallerWeights l) q
    let es := characterList l' p'
    let U := canonicalJacquetFamily μ (-1) (smallerWeights l) f.val f.2 q
    let V := continuedJacquet μ 1 l' p' f'
    let Ψ := complexSquareProductTest (operatorToEntry Φ) φ
    (∃ (F : ℂ × ℂ → ℂ) (τ σ τd σd : ℝ),
      (∀ γ : ℂ → ℂ × ℂ, Differentiable ℂ γ → Differentiable ℂ (F ∘ γ)) ∧
      (∀ z : ℂ, HasStripExponentialGrowth (fun s => F (z, s))) ∧
      (∀ z s : ℂ, τ < z.re → σ < s.re → F (z, s) = equalDoubleDenominator d ds es z s *
        complexEqualUnfoldedIntegral D.groupHaar D₁
          (shiftedCharacter d z).character.toMonoidHom Ψ U V s) ∧
      (∀ z s : ℂ, τd < (-z).re → σd < s.re → F (z, 1 - s) = (equalDoublePhase d ds es)⁻¹ *
        (equalDoubleDualDenominator d ds es z s * complexEqualUnfoldedIntegral D.groupHaar D₁
          (shiftedCharacter d.inv (-z)).character.toMonoidHom (complexMatrixFourier 1 Ψ) (ud U) (wd V) s))) →
    ∀ z : ℂ,
      let W := recursiveJacquetCoefficient D₁ (-1) l (Fin.cons z q) Φ f
      HasComplexPairNormalizedGrowth (characterList l (Fin.cons z q)) es 1 (complexCentralSign es ^ m)
        (complexEqualIntegral D W V φ) (complexEqualDualIntegral 1 D W V φ)

set_option maxHeartbeats 1000000 in
theorem complexLocalEqualGeneratorTrace : ComplexLocalEqualGeneratorTraceStatement (r := r) := by
  intro D D₁ l l' q p' Φ hΦ hfull f f' φ μ d ds es U V Ψ ⟨F, τ, σ, τd, σd, hF, hStrip, hPr, hDu⟩
  let Φ₀ := operatorToEntry Φ
  obtain ⟨Φd, hΦd⟩ := exists_schwartz_complexRectangularFourier (-1) Φ₀
  obtain ⟨φd, hφd⟩ := exists_schwartz_complexFourierTransform 1 φ
  let U₀ : complexWhittakerModel r ds 1 := ⟨U, by
    simpa only [U, μ, ds, complexSelfDualMeasure_neg_scale, neg_neg] using
      canonicalJacquetProfile_mem (-1) l q f⟩
  let V₀ : complexWhittakerModel (r + 1) es (-1) := ⟨V,
    Submodule.mem_iSup_of_mem (continuedJacquet μ 1 l' p')
      (Submodule.mem_iSup_of_mem (complexJacquetCanonicalIntertwiner μ 1 l' p') ⟨f', rfl⟩)⟩
  have hds : ds.length = m := List.length_ofFn
  have hes : es.length = n := List.length_ofFn
  obtain ⟨c, hc, hUnfold⟩ := complexLocalEqualChamberUnfolding (r := r) D D₁ 1
  obtain ⟨⟨τ₁, σ₁, hU₁⟩, τ₂, σ₂, hU₂⟩ := hUnfold d ds es hds hes U₀ V₀ Φ₀ Φd φ φd hΦd hφd
  let W (z : ℂ) := recursiveJacquetCoefficient D₁ (-1) l (Fin.cons z q) Φ f
  let b : ℂ := (d.character (-1) : ℂ) ^ m
  let E : ℂ := complexCentralSign ds * equalDoublePhase d ds es
  let S := {z : ℂ | max τ τ₁ < z.re}
  let Sd := {z : ℂ | max τd τ₂ < (-z).re}
  let p (z : ℂ) := (Fin.cons (α := fun _ : Fin n => ℂ) z q : P)
  let Z (x : ℂ × ℂ) := (c : ℂ) *
    ((complexPairLFactor (characterList l (p x.1)) es).denominator x.2 *
      complexEqualIntegral D (W x.1) V φ x.2)
  let Zd (x : ℂ × ℂ) := E⁻¹ * ((c : ℂ) *
    ((complexPairLFactor ((characterList l (p x.1)).map ComplexCharacterData.inv)
      (es.map ComplexCharacterData.inv)).denominator x.2 * complexEqualDualIntegral 1 D (W x.1) V φ x.2))
  have hE (z s : ℂ) : E = complexCentralSign es ^ m *
      (complexPairEpsilon (characterList l (p z)) es 1 ‖((1 : ℂˣ) : ℂ)‖₊
        (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ) := by
    rw [characterList_adjoining]
    exact equalDoublePhase_mul_unfolding_sign d ds es hds hes z s
  have hE₀ : E ≠ 0 := by
    rw [hE 0 0]
    exact mul_ne_zero (pow_ne_zero _ (complexCentralSign_ne_zero es)) (Units.ne_zero _)
  have hc₀ : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hs₀ : complexCentralSign ds ≠ 0 := complexCentralSign_ne_zero ds
  have hW (z : ℂ) : W z = complexJacquetRecursion 1 D₁ Φ₀ U
      (shiftedCharacter d z).character.toMonoidHom := by
    have hq : smallerExponents (p z) = q := by funext i; rfl
    simp only [W, recursiveJacquetCoefficient, neg_neg, hq, Φ₀, U, μ, d, p, addedCharacter,
      Fin.cons_zero, shiftedCharacter, characterOfParams_exponent, characterOfParams_weight, zero_add,
      complexSelfDualMeasure_neg_scale]
  have hWd (z : ℂ) (g : G) : wd (W z) g = b *
      complexJacquetRecursion (-1) D₁ Φd (ud U)
        (shiftedCharacter d.inv (-z)).character.toMonoidHom g := by
    rw [hW z]
    have hχ := (complexJacquetCanonicalBounds μ (-1) (smallerWeights l) f.val f.2 q).2.1
    have hχ' : ∀ (u : Langlands.GeneralLinear.upperUnipotent m ℂ) (x : H),
        U (u.val * x) = traceCharacter 1 (Langlands.HarmonicAnalysis.unipotentFourierSum r u) * U x := by
      simpa only [neg_neg] using hχ
    change complexJacquetRecursion 1 D₁ Φ₀ U (shiftedCharacter d z).character.toMonoidHom
      (Langlands.GeneralLinear.weylInverseTranspose n ℂ g) = _
    rw [complexJacquetRecursion_dual 1 D₁ Φ₀ U _ hχ' g, inverse_shifted_character, ← hΦd]
    change ((shiftedCharacter d z).character (-1) : ℂ) ^ m *
      complexJacquetRecursion (-1) D₁ Φd (ud U) (shiftedCharacter d.inv (-z)).character.toMonoidHom g = _
    rw [sign_adjoining]
  have hPrim (z s : ℂ) (hz : z ∈ S) (hs : max σ σ₁ < s.re) : F (z, s) = Z (z, s) := by
    have h := hU₁ z s ((le_max_right _ _).trans_lt hz) ((le_max_right _ _).trans_lt hs)
    change (c : ℂ) * complexEqualIntegral D
      (complexJacquetRecursion 1 D₁ Φ₀ U (shiftedCharacter d z).character.toMonoidHom) V φ s = _ at h
    rw [← hW z] at h
    rw [hPr z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs), ← h,
      equalDoubleDenominator_eq_pair]
    dsimp only [Z, p]
    rw [characterList_adjoining]
    ring
  have hDual (z s : ℂ) (hz : z ∈ Sd) (hs : max σd σ₂ < s.re) : F (z, 1 - s) = Zd (z, s) := by
    have h := hU₂ (-z) s ((le_max_right _ _).trans_lt hz) ((le_max_right _ _).trans_lt hs)
    let Wd := complexJacquetRecursion (-1) D₁ Φd (ud U) (shiftedCharacter d.inv (-z)).character.toMonoidHom
    change ((c : ℂ) * b) * complexEqualIntegral D Wd (wd V) φd s =
      complexCentralSign ds * complexEqualUnfoldedIntegral D.groupHaar D₁
        (shiftedCharacter d.inv (-z)).character.toMonoidHom (complexMatrixFourier 1 Ψ) (ud U) (wd V) s at h
    rw [mul_assoc, complexEqualIntegral_scale_left_of_eq D b Wd (wd (W z)) (wd V) φd s
      (fun g => (hWd z g).symm), hφd] at h
    rw [hDu z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs),
      equalDoubleDualDenominator_eq_pair]
    change _ = E⁻¹ * ((c : ℂ) * (_ * complexEqualDualIntegral 1 D (W z) V φ s))
    rw [characterList_adjoining]
    change (c : ℂ) * complexEqualDualIntegral 1 D (W z) V φ s = _ at h
    have h' : complexEqualUnfoldedIntegral D.groupHaar D₁
        (shiftedCharacter d.inv (-z)).character.toMonoidHom (complexMatrixFourier 1 Ψ) (ud U) (wd V) s =
        (complexCentralSign ds)⁻¹ * ((c : ℂ) * complexEqualDualIntegral 1 D (W z) V φ s) := by
      rw [h, ← mul_assoc, inv_mul_cancel₀ hs₀, one_mul]
    rw [h']
    dsimp only [E, d, ds]
    rw [mul_inv]
    ring
  have hp : Differentiable ℂ (p ∘ (Prod.fst : ℂ × ℂ → ℂ)) :=
    (differentiable_adjoining q).comp differentiable_fst
  have hDen := differentiable_pairDenominator l l' _ (fun _ : ℂ × ℂ => p') hp
    (differentiable_const p') _ differentiable_snd
  have hDend := differentiable_pairDualDenominator l l' _ (fun _ : ℂ × ℂ => p') hp
    (differentiable_const p') _ differentiable_snd
  have hHol (R : ℝ) : ∃ σg : ℝ,
      DifferentiableOn ℂ Z (Metric.ball (0 : ℂ) R ×ˢ {s : ℂ | σg < s.re}) ∧
      DifferentiableOn ℂ Zd (Metric.ball (0 : ℂ) R ×ˢ {s : ℂ | σg < s.re}) := by
    obtain ⟨σg, _, hZg, hZdg⟩ := complexLocalEqualGeneratorFamily 1 D D₁ l l' q p' Φ hΦ hfull f f' φ R
    exact ⟨σg, (hDen.differentiableOn.mul hZg).const_mul c,
      ((hDend.differentiableOn.mul hZdg).const_mul c).const_mul E⁻¹⟩
  have hS : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hSd : IsOpen Sd := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_neg)
  have hSne : S.Nonempty := ⟨(max τ τ₁ + 1 : ℝ), by
    simpa only [S, mem_ofPred_eq, Complex.ofReal_re] using lt_add_one (max τ τ₁)⟩
  have hSdne : Sd.Nonempty := ⟨-((max τd τ₂ + 1 : ℝ) : ℂ), by
    simpa only [Sd, mem_ofPred_eq, neg_neg, Complex.ofReal_re] using lt_add_one (max τd τ₂)⟩
  have hTr := Langlands.Analysis.affineTraceRecovery F Z Zd S Sd (max σ σ₁) (max σd σ₂)
    hS hSd hSne hSdne hF hHol (fun z hz s hs => hPrim z s hz hs) (fun z hz s hs => hDual z s hz hs)
  intro z
  obtain ⟨θ, hθ⟩ := hTr z
  let N (s : ℂ) := (c : ℂ)⁻¹ * F (z, s)
  let Nd (s : ℂ) := E * N (1 - s)
  have hN : Differentiable ℂ N :=
    (hF (fun s => (z, s)) ((differentiable_const z).prodMk differentiable_id)).const_mul _
  have hNd : Differentiable ℂ Nd := (hN.comp (differentiable_id.const_sub 1)).const_mul E
  have hNg : HasStripExponentialGrowth N := stripGrowth_const_mul (hStrip z) _
  refine ⟨N, Nd, hN, hNd, hNg, stripGrowth_const_mul (stripGrowth_reflect hNg) E, ⟨θ, ?_⟩, ?_⟩
  · intro s hs
    obtain ⟨h, hd⟩ := hθ s hs
    refine ⟨?_, ?_⟩
    · dsimp only [N]
      rw [h]
      dsimp only [Z]
      rw [← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
    · dsimp only [N, Nd]
      rw [hd]
      dsimp only [Zd]
      field_simp [hc₀, hE₀]
      rfl
  · intro s
    dsimp only [Nd]
    rw [sub_sub_cancel, ← hE]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
