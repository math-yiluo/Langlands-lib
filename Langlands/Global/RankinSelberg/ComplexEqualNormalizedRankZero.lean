import Langlands.Global.RankinSelberg.ComplexAdjacentNormalizedProducts
import Langlands.Global.RankinSelberg.ComplexLocalEqualRankZero
import Langlands.Global.RankinSelberg.ComplexSquareZetaNormalization
import Langlands.Global.RankinSelberg.ComplexTateProductScaledReflection
import Langlands.Representation.GodementJacquet.ComplexScalarFourierInversion

/-! # Entire normalization at the base of the complex rank induction -/

noncomputable section

open MeasureTheory
open scoped NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal
open Langlands.GodementJacquet (traceCharacter_neg_scale complexSelfDualMeasure_neg_scale)
open Langlands.LocalFactor.Archimedean
open ComplexAdjacentUnfolding (HasComplexPairNormalization)
open ComplexRankZero (lineSchwartz lineSchwartz_apply equalIntegral_eq
  complexPairLFactor_singleton inv_mul_exponent inv_mul_weight_natAbs)
open ComplexSquareZeta (epsilon_ofFn_shift)
open ComplexTateProduct (affineParameter normalizedZeta gammaNormalizer additiveWeight
  complexTateProductEntireFamily complexTateProductScaledReflection)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The equal-rank induction hypothesis with absolute convergence and the two entire
normalizations, for a prescribed rank index and character parameter. -/
def ComplexLocalEqualNormalizedAtRankCharacterStatement (r : ℕ) (a : ℂˣ) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
  ∀ (D : ComplexQuotientMeasureData r) (W V : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : 𝓢(Fin (r + 1) → ℂ, ℂ)),
    W ∈ complexWhittakerModel r ds a → V ∈ complexWhittakerModel r es (-a) →
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand W V Φ s) D.measure ∧
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) V)
        (complexFourierTransform a Φ) s) D.measure) ∧
    HasComplexPairNormalization ds es a (complexCentralSign es ^ r)
      (complexEqualIntegral D W V Φ) (complexEqualDualIntegral a D W V Φ)

/-- The normalized equal-rank induction hypothesis at one rank for every nonzero
character parameter. -/
def ComplexLocalEqualNormalizedAtRankStatement (r : ℕ) : Prop :=
  ∀ a : ℂˣ, ComplexLocalEqualNormalizedAtRankCharacterStatement r a

private local instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

private theorem zeta_pi_one (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) (w : ℤ) (t s : ℂ) :
    ComplexRankZero.ComplexTate.zeta (lineSchwartz Φ) w t s =
      2 * ComplexTateProduct.zeta Φ (fun _ => w) (fun _ => s + t) := by
  rw [ComplexRankZero.ComplexTate.zeta, ComplexRankZero.ComplexTate.integral_two_smul, ComplexTateProduct.zeta]
  congr 1
  let f := ComplexTateProduct.integrand (Φ : (Fin (0 + 1) → ℂ) → ℂ) (fun _ => w) (fun _ => s + t)
  have he := (volume_preserving_funUnique (Fin (0 + 1)) ℂ).symm.integral_comp' f
  rw [← he]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  change ComplexRankZero.ComplexTate.integrand (lineSchwartz Φ) w t s z = f (fun _ => z)
  by_cases hz : z = 0 <;>
    simp [f, ComplexTateProduct.integrand, ComplexRankZero.ComplexTate.integrand, additiveWeight,
      lineSchwartz_apply, hz, mul_assoc]

/-- The negative trace Fourier transform at `-a` is the positive row transform at `a`. -/
theorem traceFourier_neg_eq_complexFourierTransform {n : ℕ} (a : ℂˣ) (Φ : 𝓢(Fin n → ℂ, ℂ)) :
    (ComplexTraceFourier.transform (-a) Φ : (Fin n → ℂ) → ℂ) = complexFourierTransform a Φ := by
  funext y
  rw [ComplexTraceFourier.transform_apply, complexSelfDualMeasure_neg_scale]
  unfold complexFourierTransform ArchimedeanLocal.fourierTransform
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  have h := traceCharacter_neg_scale a (-∑ i, z i * y i)
  rw [neg_neg] at h
  exact congrArg (Φ z * ·) h

private theorem rankZero_dual_character (c : ComplexCharacterData)
    {W : Langlands.GeneralLinear (0 + 1) ℂ → ℂ} {C : ℂ}
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (g : Langlands.GeneralLinear (0 + 1) ℂ) :
    ArchimedeanLocal.dualFunction (0 + 1) W g =
      C * (c.inv.character (GeneralLinear.determinant g) : ℂ) := by
  rw [ComplexRankZero.dualFunction_apply, hW, Langlands.RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose,
    ComplexRankZero.character_inv_apply, ComplexCharacterData.inv_character_apply]

private theorem normalizedZeta_one (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) (w : ℤ) (s : ℂ) :
    normalizedZeta Φ (fun _ => w) (fun _ => s) =
      gammaNormalizer w s * ComplexTateProduct.zeta Φ (fun _ => w) (fun _ => s) := by
  unfold normalizedZeta
  rw [show (∏ _ : Fin (0 + 1), gammaNormalizer w s) = gammaNormalizer w s from
    Fin.prod_univ_one (fun _ : Fin 1 => gammaNormalizer w s)]

/-- The normalized equal-rank base `GL₁(ℂ) × GL₁(ℂ)` needed by the adjacent induction. -/
def ComplexEqualNormalizedRankZeroStatement : Prop :=
  ComplexLocalEqualNormalizedAtRankStatement 0

set_option maxHeartbeats 700000 in
theorem complexEqualNormalizedRankZero : ComplexEqualNormalizedRankZeroStatement := by
  intro a ds es hd he D W V Φ hW hV
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hd
  obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp he
  obtain ⟨σ, _, _, hI, hId, _⟩ :=
    complexLocalEqualRankZero [c] [c'] rfl rfl a D W V Φ hW hV
  refine ⟨⟨σ, fun s hs => ⟨hI s hs, hId s hs⟩⟩, ?_⟩
  obtain ⟨C, hC⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hW
  obtain ⟨C', hC'⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hV
  obtain ⟨κ, _, hκ⟩ := ComplexRankZero.exists_measure_eq D
  let K : ℂ := (κ : ℂ) * (C * C')
  let w := (c.mul c').weight
  let t := (c.mul c').exponent
  let Ψ := ComplexTraceFourier.transform (-a) Φ
  have hΨ : (Ψ : (Fin (0 + 1) → ℂ) → ℂ) = complexFourierTransform a Φ :=
    traceFourier_neg_eq_complexFourierTransform a Φ
  have hZ (s : ℂ) : complexEqualIntegral D W V Φ s =
      K * ComplexTateProduct.zeta Φ (fun _ => w) (fun _ => s + t) := by
    rw [equalIntegral_eq c c' hκ hC hC', zeta_pi_one]
    dsimp only [K, w, t]
    ring
  have hZd (s : ℂ) : complexEqualDualIntegral a D W V Φ s =
      K * ComplexTateProduct.zeta Ψ (fun _ => -w) (fun _ => s + -t) := by
    change complexEqualIntegral D (ArchimedeanLocal.dualFunction (0 + 1) W)
      (ArchimedeanLocal.dualFunction (0 + 1) V)
      (complexFourierTransform a Φ) s = _
    rw [← hΨ, equalIntegral_eq c.inv c'.inv hκ (rankZero_dual_character c hC)
      (rankZero_dual_character c' hC'), zeta_pi_one, inv_mul_exponent]
    have hw : (c.inv.mul c'.inv).weight = -w := neg_add c.weight c'.weight |>.symm
    rw [hw]
    dsimp only [K, t]
    ring
  obtain ⟨H, hH⟩ := complexTateProductEntireFamily 0
  let N (s : ℂ) := K * H Φ (fun _ => w) (fun _ => s + t)
  let Nd (s : ℂ) := K * H Ψ (fun _ => -w) (fun _ => s + -t)
  have hAffine (v s : ℂ) :
      affineParameter (fun _ : Fin (0 + 1) => v) (fun _ => 1) s = fun _ => s + v := by
    funext j
    simp [affineParameter, add_comm v]
  have hN : Differentiable ℂ N := by
    simpa only [N, hAffine] using
      (hH.1 Φ (fun _ => w) (fun _ => t) (fun _ => 1)).const_mul K
  have hNd : Differentiable ℂ Nd := by
    simpa only [Nd, hAffine] using
      (hH.1 Ψ (fun _ => -w) (fun _ => -t) (fun _ => 1)).const_mul K
  refine ⟨N, Nd, hN, hNd, ⟨|t.re|, fun s hs => ?_⟩, fun s => ?_⟩
  · have h₁ : 0 < (s + t).re := by
      rw [Complex.add_re]
      linarith [neg_abs_le t.re]
    have h₂ : 0 < (s + -t).re := by
      rw [Complex.add_re, Complex.neg_re]
      linarith [le_abs_self t.re]
    constructor
    · dsimp only [N]
      rw [hH.2 _ _ _ (fun _ => h₁), hZ, complexPairLFactor_singleton, normalizedZeta_one]
      simp only [gammaNormalizer, w, t, add_assoc]
      ring
    · dsimp only [Nd]
      simp only [List.map_cons, List.map_nil]
      rw [hH.2 _ _ _ (fun _ => h₂), hZd, complexPairLFactor_singleton, inv_mul_exponent,
        inv_mul_weight_natAbs, normalizedZeta_one]
      simp only [gammaNormalizer, Int.natAbs_neg, w, t, add_assoc]
      ring
  · have he := complexTateProductScaledReflection 0 H hH (-a) Φ (fun _ => w) (fun _ => s + t)
    have hs : (fun _ : Fin (0 + 1) => 1 - (s + t)) = fun _ => (1 - s) + -t := by
      funext j
      ring
    rw [hs] at he
    have hε := epsilon_ofFn_shift (fun _ : Fin (0 + 1) => c.mul c') (-a) s
    have hε' :
        (∏ j : Fin (0 + 1), ((Langlands.Archimedean.characterOfParams w 0).epsilon a ‖(a : ℂ)‖₊
          (nnnorm_pos.mpr a.ne_zero) (s + t) : ℂ)) =
          (complexPairEpsilon [c] [c'] a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) := by
      simpa only [w, t, complexPairEpsilon, ComplexRankZero.complexPairBlocks_singleton,
        List.ofFn_succ, List.ofFn_zero, neg_neg, Units.val_neg, nnnorm_neg] using hε
    dsimp only [Nd, Ψ]
    rw [he]
    simp only [N, pow_zero, one_mul, neg_neg, Units.val_neg, nnnorm_neg, hε']
    ring

end Langlands.Global.RankinSelbergGlobal
