import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Global.RankinSelberg.RealJacquetConventionReduction

/-! # Fourier sign in the complex unequal-rank local equation -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

private theorem character_neg (d : ComplexCharacterData) (a : ℂˣ) :
    d.character (-a) = d.character (-1) * d.character a := by
  rw [← map_mul, neg_one_mul]

theorem block_epsilon_neg (d : ComplexCharacterData) (a : ℂˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) :
    (d.epsilon (-a) c hc s : ℂ) = (d.character (-1) : ℂ) * (d.epsilon a c hc s : ℂ) := by
  rw [d.coe_epsilon, d.coe_epsilon, character_neg d a]
  simp only [Units.val_mul, Units.val_neg, norm_neg]
  ring

/-- Negating the trace-character parameter multiplies the list epsilon factor by the
product of the characters at `-1`, for the same Haar scale. -/
theorem epsilon_neg (ds : List ComplexCharacterData) (a : ℂˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) :
    (complexEpsilon ds (-a) c hc s : ℂ) =
      complexCentralSign ds * (complexEpsilon ds a c hc s : ℂ) := by
  induction ds with
  | nil => simp [complexCentralSign]
  | cons d ds ih =>
    simp only [complexEpsilon_cons, complexCentralSign, List.map_cons, List.prod_cons,
      Units.val_mul] at ih ⊢
    rw [block_epsilon_neg, ih]
    ring

theorem complexCentralSign_sq (ds : List ComplexCharacterData) : complexCentralSign ds ^ 2 = 1 := by
  induction ds with
  | nil => simp [complexCentralSign]
  | cons d ds ih =>
    have h : (d.character (-1) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow]
      simp [pow_two]
    simpa only [complexCentralSign, List.map_cons, List.prod_cons, mul_pow, h, one_mul] using ih

private theorem complexCentralSign_append (ds es : List ComplexCharacterData) :
    complexCentralSign (ds ++ es) = complexCentralSign ds * complexCentralSign es := by
  simp [complexCentralSign, List.prod_append]

private theorem complexCentralSign_map_mul (d : ComplexCharacterData) (es : List ComplexCharacterData) :
    complexCentralSign (es.map d.mul) = (d.character (-1) : ℂ) ^ es.length * complexCentralSign es := by
  induction es with
  | nil => simp [complexCentralSign]
  | cons e es ih =>
    have h : (d.mul e).character (-1) = d.character (-1) * e.character (-1) := rfl
    simp only [List.map_cons, complexCentralSign, List.prod_cons, List.length_cons, pow_succ,
      h, Units.val_mul] at ih ⊢
    rw [ih]
    ring

theorem complexCentralSign_pairBlocks (ds es : List ComplexCharacterData) :
    complexCentralSign (complexPairBlocks ds es) =
      complexCentralSign ds ^ es.length * complexCentralSign es ^ ds.length := by
  induction ds with
  | nil => simp [complexPairBlocks, complexCentralSign]
  | cons d ds ih =>
    rw [show complexPairBlocks (d :: ds) es = es.map d.mul ++ complexPairBlocks ds es from rfl,
      complexCentralSign_append, complexCentralSign_map_mul, ih]
    simp only [complexCentralSign, List.map_cons, List.prod_cons, List.length_cons, pow_succ, mul_pow]
    ring

theorem pair_epsilon_neg (ds es : List ComplexCharacterData) (a : ℂˣ)
    (c : NNReal) (hc : 0 < c) (s : ℂ) :
    (complexPairEpsilon ds es (-a) c hc s : ℂ) =
      (complexCentralSign ds ^ es.length * complexCentralSign es ^ ds.length) *
        (complexPairEpsilon ds es a c hc s : ℂ) := by
  rw [complexPairEpsilon, complexPairEpsilon, epsilon_neg, complexCentralSign_pairBlocks]

theorem selfDualMeasure_neg (a : ℂˣ) : complexSelfDualMeasure (-a) = complexSelfDualMeasure a := by
  unfold complexSelfDualMeasure
  congr 1
  simp

theorem fourier_neg (a : ℂˣ) {n : ℕ} (Φ : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) :
    complexFourierTransform (-a) Φ x = complexFourierTransform a Φ (-x) := by
  unfold complexFourierTransform
  rw [selfDualMeasure_neg]
  unfold fourierTransform
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  change ((complexScaledCharacter (-a)).complex _ : ℂ) = (complexScaledCharacter a).complex _
  have hx : (∑ j, y j * (-x) j) = -(∑ j, y j * x j) := by
    simp [Finset.sum_neg_distrib]
  rw [hx]
  simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    complexScaledCharacter_apply, Units.val_neg, neg_mul, mul_neg]

/-- Jacquet's coefficient with the negative Fourier convention equals the coefficient in
the Library's positive convention. The power `t + 1` is the smaller rank. -/
theorem unequal_coefficient (r t : ℕ) (ds es : List ComplexCharacterData)
    (hd : ds.length = r + 1) (he : es.length = t + 1) (a : ℂˣ)
    (c : NNReal) (hc : 0 < c) (s : ℂ) :
    (complexCentralSign ds ^ (t + 1) * complexCentralSign es) *
        (complexPairEpsilon ds es (-a) c hc s : ℂ) =
      complexCentralSign es ^ r * (complexPairEpsilon ds es a c hc s : ℂ) := by
  rw [pair_epsilon_neg, hd, he]
  have hd' : (complexCentralSign ds ^ (t + 1)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, complexCentralSign_sq, one_pow]
  rw [pow_succ (complexCentralSign es) r]
  calc
    _ = (complexCentralSign ds ^ (t + 1)) ^ 2 *
        (complexCentralSign es ^ r * complexCentralSign es ^ 2) *
          (complexPairEpsilon ds es a c hc s : ℂ) := by ring
    _ = _ := by rw [hd', complexCentralSign_sq, mul_one, one_mul]

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable
  archimedeanComplexQBorel

/-- The unequal-rank package with independently specified epsilon parameter and sign.
Both integrals, the measure scale, and the L-factors use the data of the target. -/
def UnequalEquation {r t : ℕ} (h : t < r) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (ds es : List ComplexCharacterData) (b : ℂˣ) (sign : ℂ) : Prop :=
  RealJacquet.EquationPackage D.measure (complexUnequalDualMeasure (r := r) a D)
    (complexUnequalIntegrand h W W') (complexUnequalDualKernel h W W')
    (complexUnequalIntegral h D W W') (complexUnequalDualIntegral h a D W W')
    (fun s => ((complexPairLFactor ds es).denominator s)⁻¹)
    (fun s => ((complexPairLFactor (ds.map ComplexCharacterData.inv)
      (es.map ComplexCharacterData.inv)).denominator s)⁻¹)
    (fun s => (complexPairEpsilon ds es b ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ))
    sign

/-- Jacquet's negative-Fourier equation on the Library's carriers. The sign is the one
in the proof after (10.10). -/
def ComplexLocalUnequalJacquetEquationStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData),
    ds.length = r + 1 → es.length = t + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ),
    W ∈ complexWhittakerModel r ds a → W' ∈ complexWhittakerModel t es (-a) →
    UnequalEquation h a D W W' ds es (-a) (complexCentralSign ds ^ (t + 1) * complexCentralSign es)

def ComplexUnequalJacquetConventionReductionStatement : Prop :=
  ComplexLocalUnequalJacquetEquationStatement → ComplexLocalUnequalFunctionalEquationStatement

theorem complexUnequalJacquetConventionReduction : ComplexUnequalJacquetConventionReductionStatement := by
  intro hJ r t h ds es hd he a D W W' hW hW'
  change UnequalEquation h a D W W' ds es a (complexCentralSign es ^ r)
  exact RealJacquet.EquationPackage.change_factor
    (hJ r t h ds es hd he a D W W' hW hW')
    (unequal_coefficient r t ds es hd he a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero))

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
