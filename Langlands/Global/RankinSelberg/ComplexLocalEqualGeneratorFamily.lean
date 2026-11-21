import Langlands.Global.RankinSelberg.ComplexJacquetRecursiveSpan
import Langlands.Global.RankinSelberg.ComplexLocalEqualCanonicalFamily

/-! # Ordinary equal-rank traces for the compact Godement recursion generators -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent)
open Langlands.GeneralLinear (inverseTranspose continuous_inverseTranspose weylLong weylInverseTranspose)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure complexFourierTransform
  complexEqualIntegrand complexEqualIntegral complexEqualDualIntegral)
open ComplexCompactProfileFamily (characterList compactRestriction compactRestriction_isCompactProfile)
open ComplexGodement (SmallerProfile HasFullRowRank smallerWeights smallerExponents)
open ComplexGodementGeneratorFamily (generatorFamily complexGodementGeneratorFamily)
open ComplexGodementAddedCharacter (continuedValue_eq_signed_recursion)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexUnequalFamily (HasLeftCharacter)
open ComplexJacquet (complexLocalEqualFamily uniformSimpleRootBound_compact uniformSimpleRootBound_dual)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => r + 1 + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "P" => Fin n → ℂ
local notation "L" => Fin n → ℤ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite n (characterList l p)

private theorem hasLeftCharacter_dual {j : ℕ} {a : ℂˣ}
    {W : Langlands.GeneralLinear (j + 1) ℂ → ℂ} (h : HasLeftCharacter a W) :
    HasLeftCharacter (-a) (ArchimedeanLocal.dualFunction (j + 1) W) := by
  intro u g
  change W (weylInverseTranspose (j + 1) ℂ (u.val * g)) = complexWhittakerCharacter (-a) u.val *
    W (weylInverseTranspose (j + 1) ℂ g)
  rw [Langlands.Whittaker.weylInverseTranspose_left_unipotent, h]
  congr 1
  simp only [complexWhittakerCharacter, Langlands.Whittaker.reflectedUnipotent_sum,
    Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    Langlands.LocalFactor.Archimedean.complexScaledCharacter_apply, Units.val_neg, neg_mul, mul_neg]

private theorem differentiable_adjoin (q : Fin m → ℂ) :
    Differentiable ℂ (fun z : ℂ => (Fin.cons (α := fun _ : Fin n => ℂ) z q : P)) := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Differentiable ℂ (fun z : ℂ => z)
    exact differentiable_id
  · simpa only [Fin.cons_succ] using (differentiable_const (q j) : Differentiable ℂ fun _ : ℂ => q j)

private theorem generatorLine_properties (D₁ : ComplexQuotientMeasureData r) (a : ℂˣ) (l : L)
    (q : Fin m → ℂ) (Φ : 𝓢(Rect, ℂ)) (hΦ : HasCompactSupport Φ)
    (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X) (f : SmallerProfile l) (K : Set ℂ) (hK : IsCompact K) :
    let W (z : ℂ) := recursiveJacquetCoefficient D₁ (-a) l (Fin.cons z q) Φ f
    (∀ z, Continuous (W z)) ∧ (∀ g, Differentiable ℂ (W · g)) ∧
      (∀ z, HasLeftCharacter a (W z)) ∧ HasUniformSimpleRootBound K W := by
  let t := RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := t.locallyCompactSpace
  let : SecondCountableTopology H := t.secondCountableTopology
  let : D₁.groupHaar.IsHaarMeasure := D₁.groupHaar_isHaar
  let : D₁.groupHaar.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure D₁.groupHaar
  let : D₁.groupHaar.IsMulRightInvariant := Archimedean.isMulRightInvariant_archimedeanGL ℂ m D₁.groupHaar
  let μ := complexSelfDualMeasure (-a)
  let V := canonicalJacquetFamily μ (-a) (smallerWeights l) f.val f.2
  let F := generatorFamily D₁.groupHaar μ (-a) l Φ V
  let S : ℂ := (characterOfParams (l 0) 0).character ((-1 : ℂˣ) ^ m)
  have hS : S ≠ 0 := Units.ne_zero _
  have hV := canonicalJacquetFamily_properties μ (-a) (smallerWeights l) f.val f.2
  obtain ⟨hFd, hFc, hFχ, hFb, _⟩ := complexGodementGeneratorFamily (r := r) D₁.groupHaar μ (-a) l Φ hΦ hfull
    f V hV.1 hV.2.1 hV.2.2.1 hV.2.2.2
  let W (z : ℂ) := recursiveJacquetCoefficient D₁ (-a) l (Fin.cons z q) Φ f
  have eqF (z : ℂ) (g : G) : F (Fin.cons z q) g = S * W z g := by
    let d := characterOfParams (l 0) 0
    have h := complexJacquetCanonicalBounds μ (-a) (smallerWeights l) f.val f.2 q
    have he := continuedValue_eq_signed_recursion (-a) D₁ d (operatorToEntry Φ)
      h.1 h.2.1 h.2.2 g z
    have hq : smallerExponents (Fin.cons (α := fun _ : Fin n => ℂ) z q) = q := by
      funext i
      exact Fin.cons_succ (α := fun _ : Fin n => ℂ) z q i
    simpa only [F, W, S, V, d, μ, generatorFamily, recursiveJacquetCoefficient, hq,
      Fin.cons_zero, Fin.cons_succ, ComplexGodement.addedCharacter,
      characterOfParams_exponent, characterOfParams_weight, zero_add] using he
  have hW (z : ℂ) : W z = fun g => S⁻¹ * F (Fin.cons z q) g := by
    funext g
    rw [eqF, ← mul_assoc, inv_mul_cancel₀ hS, one_mul]
  obtain ⟨J, hJ⟩ := uniformSimpleRootBound_compact (hK.image (differentiable_adjoin q).continuous) F hFb
  change (∀ z, Continuous (W z)) ∧ (∀ g, Differentiable ℂ (W · g)) ∧
    (∀ z, HasLeftCharacter a (W z)) ∧ HasUniformSimpleRootBound K W
  refine ⟨fun z => (hW z) ▸ (continuous_const.mul (hFc (Fin.cons z q))), ?_, ?_, J, ?_⟩
  · intro g
    simp only [hW]
    exact ((hFd g).comp (differentiable_adjoin q)).const_mul S⁻¹
  · intro z u g
    have hc := hFχ (Fin.cons z q) (mem_univ _) u.val u.2 g
    rw [neg_neg] at hc
    change F (Fin.cons z q) (u.val * g) = _ at hc
    simp only [hW, hc]
    ring
  · intro k
    obtain ⟨C, hC, hd⟩ := hJ k
    refine ⟨‖S⁻¹‖ * C, mul_nonneg (norm_nonneg _) hC, fun z hz g => ?_⟩
    have hb := hd (Fin.cons z q) (mem_image_of_mem _ hz) g
    rw [hW, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-- The ordinary primal and dual integrals of a compact Godement recursion generator
vary holomorphically with the adjoining exponent and the spectral parameter. -/
def ComplexLocalEqualGeneratorFamilyStatement : Prop :=
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (l l' : L) (q : Fin m → ℂ) (p' : P) (Φ : 𝓢(Rect, ℂ)),
    HasCompactSupport Φ → (∀ X ∈ tsupport Φ, HasFullRowRank X) →
    ∀ (f : SmallerProfile l) (f' : Std[l', p']) (φ : 𝓢(Row, ℂ)) (R : ℝ),
    let W (z : ℂ) := recursiveJacquetCoefficient D₁ (-a) l (Fin.cons z q) Φ f
    let V := continuedJacquet (complexSelfDualMeasure a) a l' p' f'
    let B := Metric.ball (0 : ℂ) R
    ∃ σ : ℝ,
      (∀ z ∈ B, ∀ s : ℂ, σ < s.re →
        Integrable (complexEqualIntegrand (W z) V φ s) D.measure ∧
        Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction n (W z))
          (ArchimedeanLocal.dualFunction n V) (complexFourierTransform a φ) s) D.measure) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => complexEqualIntegral D (W x.1) V φ x.2)
        (B ×ˢ {s : ℂ | σ < s.re}) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => complexEqualDualIntegral a D (W x.1) V φ x.2)
        (B ×ˢ {s : ℂ | σ < s.re})

set_option maxHeartbeats 700000 in
theorem complexLocalEqualGeneratorFamily : ComplexLocalEqualGeneratorFamilyStatement (r := r) := by
  intro a D D₁ l l' q p' Φ hΦ hfull f f' φ R
  let μ := complexSelfDualMeasure a
  let W₀ (z : ℂ) := recursiveJacquetCoefficient D₁ (-a) l (Fin.cons z q) Φ f
  let V₀ := continuedJacquet μ a l' p' f'
  let B := Metric.ball (0 : ℂ) R
  let S := B ×ˢ (univ : Set ℂ)
  let W : ℂ × ℂ → G → ℂ := W₀ ∘ Prod.fst
  let V : ℂ × ℂ → G → ℂ := fun _ => V₀
  let Wd (x : ℂ × ℂ) := ArchimedeanLocal.dualFunction n (W x)
  let Vd (x : ℂ × ℂ) := ArchimedeanLocal.dualFunction n (V x)
  obtain ⟨hWc, hWd, hWχ, J, hJ⟩ := generatorLine_properties D₁ a l q Φ hΦ hfull f _ (isCompact_closedBall _ _)
  have hVB := canonicalJacquetFamily_properties μ a l' (compactRestriction f'.val)
    (compactRestriction_isCompactProfile f'.2)
  have hVc : Continuous V₀ := hVB.1 p'
  have hVχ : HasLeftCharacter (-a) V₀ := fun u g =>
    (complexJacquetCanonicalIntertwiner μ a l' p').1 f' u.val u.2 g
  obtain ⟨δ, hδ, N, hN⟩ := hVB.2.2.1 p'
  have hWb : HasUniformSimpleRootBound S W := by
    refine ⟨J, fun k => ?_⟩
    obtain ⟨C, hC, hC'⟩ := hJ k
    exact ⟨C, hC, fun x hx g => hC' x.1 (Metric.ball_subset_closedBall hx.1) g⟩
  have hVb : HasUniformSimpleRootBound S V := by
    refine ⟨N, fun k => ?_⟩
    obtain ⟨C, hC, hC'⟩ := hN k
    exact ⟨C, hC, fun _ _ g => hC' p' (Metric.mem_ball_self hδ) g⟩
  have hS : IsOpen S := Metric.isOpen_ball.prod isOpen_univ
  obtain ⟨σ, hi, hd⟩ := complexLocalEqualFamily a D S W V Prod.snd φ hS differentiable_snd
    (fun x => hWχ x.1) (fun _ => hVχ) (fun x => hWc x.1) (fun _ => hVc)
    (fun g => ((hWd g).comp differentiable_fst).differentiableOn) (fun _ => differentiableOn_const _)
    hWb hVb
  obtain ⟨φd, hφd⟩ := exists_schwartz_complexFourierTransform a φ
  have hArg : Continuous (weylInverseTranspose n ℂ) :=
    continuous_const.mul (continuous_inverseTranspose n ℂ)
  have hVdχ (x : ℂ × ℂ) : HasLeftCharacter (-(-a)) (Vd x) := hasLeftCharacter_dual hVχ
  obtain ⟨τ, hid, hdd⟩ := complexLocalEqualFamily (-a) D S Wd Vd Prod.snd φd hS differentiable_snd
    (fun x => hasLeftCharacter_dual (hWχ x.1)) hVdχ
    (fun x => (hWc x.1).comp hArg) (fun _ => hVc.comp hArg)
    (fun g => ((hWd (weylInverseTranspose n ℂ g)).comp differentiable_fst).differentiableOn)
    (fun _ => differentiableOn_const _) (uniformSimpleRootBound_dual hWb) (uniformSimpleRootBound_dual hVb)
  refine ⟨max σ τ, ?_, ?_, ?_⟩
  · intro z hz s hs
    have hs₁ : (z, s) ∈ S ∩ {x : ℂ × ℂ | σ < x.2.re} := ⟨⟨hz, mem_univ _⟩, (le_max_left _ _).trans_lt hs⟩
    have hs₂ : (z, s) ∈ S ∩ {x : ℂ × ℂ | τ < x.2.re} := ⟨⟨hz, mem_univ _⟩, (le_max_right _ _).trans_lt hs⟩
    have h := hid (z, s) hs₂
    rw [hφd] at h
    exact ⟨hi (z, s) hs₁, h⟩
  · exact hd.mono (fun x hx => ⟨⟨hx.1, mem_univ _⟩,
      show σ < x.2.re from (le_max_left σ τ).trans_lt hx.2⟩)
  · rw [hφd] at hdd
    exact hdd.mono (fun x hx => ⟨⟨hx.1, mem_univ _⟩,
      show τ < x.2.re from (le_max_right σ τ).trans_lt hx.2⟩)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
