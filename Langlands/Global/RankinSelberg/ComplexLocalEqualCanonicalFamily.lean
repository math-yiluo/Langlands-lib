import Langlands.Global.RankinSelberg.ComplexLocalEqualFamily
import Langlands.Global.RankinSelberg.ComplexLocalUniformDualBounds
import Langlands.Global.RankinSelberg.ComplexJacquetCanonicalSmooth
import Langlands.Global.RankinSelberg.ComplexLocalFourierSchwartz

/-! # Ordinary equal-rank zeta families along affine inducing lines -/

noncomputable section

open MeasureTheory Set
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.GeneralLinear (inverseTranspose continuous_inverseTranspose weylLong)
open ArchimedeanLocal (ComplexQuotientMeasureData complexFourierTransform complexEqualIntegrand
  complexEqualIntegral complexEqualDualIntegral)
open ComplexCompactProfileFamily (characterList compactRestriction compactRestriction_isCompactProfile)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexUnequalFamily (HasLeftCharacter)
open ComplexJacquet (complexLocalEqualFamily uniformSimpleRootBound_compact uniformSimpleRootBound_dual)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "I" => Fin n
local notation "Q" => I → ℂ
local notation "L" => I → ℤ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite n (characterList l p)
local notation "ZPair" => ℂ × ℂ

/-- Affine deformation in the vector space of inducing exponents. -/
def inducingLine (p q : Q) (z : ℂ) : Q := p + z • (q - p)

private theorem differentiable_inducingLine (p q : Q) : Differentiable ℂ (inducingLine p q) :=
  (differentiable_const p).add ((differentiable_id : Differentiable ℂ (id : ℂ → ℂ)).smul_const (q - p))

@[simp] theorem inducingLine_zero (p q : Q) : inducingLine p q 0 = p := by simp [inducingLine]
@[simp] theorem inducingLine_one (p q : Q) : inducingLine p q 1 = q := by simp [inducingLine]

/-- The canonical family with the same compact restriction along an affine inducing line. -/
def canonicalJacquetLine (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p q : Q) (f : Std[l, p])
    (z : ℂ) : G → ℂ := continuedJacquetFamilies μ a l p f (inducingLine p q z)

theorem canonicalJacquetLine_eq (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p q : Q)
    (f : Std[l, p]) (z : ℂ) : canonicalJacquetLine μ a l p q f z =
      continuedJacquet μ a l (inducingLine p q z) (transferProfile l p (inducingLine p q z) f) :=
  (continuedJacquet_transferProfile μ a l p (inducingLine p q z) f).symm

private theorem canonicalJacquetLine_properties (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : L) (p q : Q) (f : Std[l, p]) (K : Set ℂ) (hK : IsCompact K) :
    let W := canonicalJacquetLine μ a l p q f
    (∀ z, Continuous (W z)) ∧ (∀ g, Differentiable ℂ (W · g)) ∧
    (∀ z, HasLeftCharacter (-a) (W z)) ∧
    (∀ z, HasLeftCharacter a (ArchimedeanLocal.dualFunction n (W z))) ∧ HasUniformSimpleRootBound K W := by
  let W₀ := canonicalJacquetFamily μ a l (compactRestriction f.val)
    (compactRestriction_isCompactProfile f.2)
  have h := canonicalJacquetFamily_properties μ a l (compactRestriction f.val)
    (compactRestriction_isCompactProfile f.2)
  have hB := uniformSimpleRootBound_compact (hK.image (differentiable_inducingLine p q).continuous)
    W₀ h.2.2.1
  obtain ⟨N, hN⟩ := hB
  refine ⟨fun z => h.1 _, fun g => (h.2.1 g).comp (differentiable_inducingLine p q), ?_, ?_, N, ?_⟩
  · intro z u g
    rw [canonicalJacquetLine_eq]
    exact (complexJacquetCanonicalIntertwiner μ a l (inducingLine p q z)).1 _ u.val u.2 g
  · intro z u g
    rw [canonicalJacquetLine_eq]
    let C := continuedJacquet μ a l (inducingLine p q z)
    have hC := complexJacquetCanonicalIntertwiner μ a l (inducingLine p q z)
    have hw : C (transferProfile l p (inducingLine p q z) f) ∈
        complexWhittakerModel r (characterList l (inducingLine p q z)) (-a) :=
      (le_iSup₂ (f := fun B (_ : IsComplexWhittakerIntertwiner r
        (characterList l (inducingLine p q z)) (-a) B) => LinearMap.range B) C hC)
        ⟨_, rfl⟩
    simpa only [neg_neg] using complexWhittakerModel_dual_left_mul hw u g
  · intro J
    obtain ⟨C, hC, hb⟩ := hN J
    exact ⟨C, hC, fun z hz g => hb _ (mem_image_of_mem _ hz) g⟩

/-- Both ordinary equal-rank integrals of two canonical affine families converge and are
jointly holomorphic on uniform right half-planes on a bounded disk of inducing parameters. -/
def ComplexLocalEqualCanonicalFamilyStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (l l' : L) (p q p' q' : Q) (f : Std[l, p]) (f' : Std[l', p']) (Φ : 𝓢(I → ℂ, ℂ))
    (R : ℝ),
    let W := canonicalJacquetLine μ (-a) l p q f
    let V := canonicalJacquetLine μ a l' p' q' f'
    let P := Metric.ball (0 : ℂ) R
    ∃ σ : ℝ,
      (∀ z ∈ P, ∀ s : ℂ, σ < s.re →
        Integrable (complexEqualIntegrand (W z) (V z) Φ s) D.measure ∧
        Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction n (W z)) (ArchimedeanLocal.dualFunction n (V z))
          (complexFourierTransform a Φ) s) D.measure) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => complexEqualIntegral D (W x.1) (V x.1) Φ x.2)
        (P ×ˢ {s : ℂ | σ < s.re}) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => complexEqualDualIntegral a D (W x.1) (V x.1) Φ x.2)
        (P ×ˢ {s : ℂ | σ < s.re})

set_option maxHeartbeats 700000 in
theorem complexLocalEqualCanonicalFamily : ComplexLocalEqualCanonicalFamilyStatement (r := r) := by
  intro μ a D l l' p q p' q' f f' Φ R
  let W := canonicalJacquetLine μ (-a) l p q f
  let V := canonicalJacquetLine μ a l' p' q' f'
  let P := Metric.ball (0 : ℂ) R
  let S : Set ZPair := P ×ˢ univ
  let F : ZPair → G → ℂ := W ∘ Prod.fst
  let H : ZPair → G → ℂ := V ∘ Prod.fst
  let DF : ZPair → G → ℂ := fun x => ArchimedeanLocal.dualFunction n (F x)
  let DH : ZPair → G → ℂ := fun x => ArchimedeanLocal.dualFunction n (H x)
  have hS : IsOpen S := Metric.isOpen_ball.prod isOpen_univ
  have hc : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  obtain ⟨hWc, hWd, hWχ, hDWχ, hWb⟩ := canonicalJacquetLine_properties μ (-a) l p q f _ hc
  obtain ⟨hVc, hVd, hVχ, hDVχ, hVb⟩ := canonicalJacquetLine_properties μ a l' p' q' f' _ hc
  have hFB : HasUniformSimpleRootBound S F := by
    obtain ⟨N, hN⟩ := hWb
    refine ⟨N, fun J => ?_⟩
    obtain ⟨C, hC, hb⟩ := hN J
    exact ⟨C, hC, fun x hx g => hb x.1 (Metric.ball_subset_closedBall hx.1) g⟩
  have hHB : HasUniformSimpleRootBound S H := by
    obtain ⟨N, hN⟩ := hVb
    refine ⟨N, fun J => ?_⟩
    obtain ⟨C, hC, hb⟩ := hN J
    exact ⟨C, hC, fun x hx g => hb x.1 (Metric.ball_subset_closedBall hx.1) g⟩
  have hFχ (x : ZPair) : HasLeftCharacter a (F x) := by
    simpa only [F, W, Function.comp_apply, neg_neg] using hWχ x.1
  obtain ⟨σ, hi, hd⟩ := complexLocalEqualFamily (E := ZPair) a D S F H Prod.snd Φ hS
    differentiable_snd hFχ (fun x => hVχ x.1) (fun x => hWc x.1) (fun x => hVc x.1)
    (fun g => ((hWd g).comp differentiable_fst).differentiableOn)
    (fun g => ((hVd g).comp differentiable_fst).differentiableOn) hFB hHB
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_complexFourierTransform a Φ
  have hArg : Continuous (fun g : G => weylLong n ℂ * inverseTranspose n ℂ g) :=
    continuous_const.mul (continuous_inverseTranspose n ℂ)
  have hDHχ (x : ZPair) : HasLeftCharacter (-(-a)) (DH x) := by
    simpa only [DH, H, V, Function.comp_apply, neg_neg] using hDVχ x.1
  obtain ⟨τ, hi', hd'⟩ := complexLocalEqualFamily (E := ZPair) (-a) D S DF DH Prod.snd Ψ hS
    differentiable_snd (fun x => hDWχ x.1) hDHχ (fun x => (hWc x.1).comp hArg)
    (fun x => (hVc x.1).comp hArg) (fun g => ((hWd _).comp differentiable_fst).differentiableOn)
    (fun g => ((hVd _).comp differentiable_fst).differentiableOn)
    (uniformSimpleRootBound_dual hFB) (uniformSimpleRootBound_dual hHB)
  refine ⟨max σ τ, ?_, ?_, ?_⟩
  · intro z hz s hs
    have h₁ : (z, s) ∈ S ∩ {v : ZPair | σ < v.2.re} := ⟨⟨hz, mem_univ _⟩, (le_max_left _ _).trans_lt hs⟩
    have h₂ : (z, s) ∈ S ∩ {v : ZPair | τ < v.2.re} := ⟨⟨hz, mem_univ _⟩, (le_max_right _ _).trans_lt hs⟩
    have ht := hi' (z, s) h₂
    rw [hΨ] at ht
    exact ⟨hi (z, s) h₁, ht⟩
  · apply hd.mono
    intro x hx
    exact ⟨⟨hx.1, mem_univ _⟩, show σ < x.2.re from (le_max_left σ τ).trans_lt hx.2⟩
  · rw [hΨ] at hd'
    apply hd'.mono
    intro x hx
    exact ⟨⟨hx.1, mem_univ _⟩, show τ < x.2.re from (le_max_right σ τ).trans_lt hx.2⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
