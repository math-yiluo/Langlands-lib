import Langlands.Global.RankinSelberg.ComplexLocalEqualCanonicalFamily
import Langlands.Global.RankinSelberg.ComplexPairParameterReflection

/-! # Transport of the canonical equal-rank normalization in the inducing exponents -/

noncomputable section

open Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ArchimedeanLocal (ComplexQuotientMeasureData complexEqualIntegral complexEqualDualIntegral)
open ComplexCompactProfileFamily (characterList compactRestriction standardSection_unitary
  standardSection_compactRestriction)
open ComplexAdjacentUnfolding (HasComplexPairNormalization complexPairParameterReflection
  complexCentralSign_characterList complexCentralSign_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "P" => I → ℂ
local notation "L" => I → ℤ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite n (characterList l p)

private theorem transferProfile_back (l : L) (p q : P) (f : Std[l, q]) :
    transferProfile l p q (transferProfile l q p f) = f := by
  have h : compactRestriction (transferProfile l q p f).val = compactRestriction f.val :=
    funext (standardSection_unitary p (compactRestriction f.val))
  apply Subtype.ext
  rw [transferProfile_val, h, standardSection_compactRestriction f.2]

private theorem differentiable_affine (p q : P) : Differentiable ℂ (inducingLine p q) :=
  (differentiable_const p).add ((differentiable_id : Differentiable ℂ (id : ℂ → ℂ)).smul_const (q - p))

/-- Exact entire pair normalization on every compact-finite pair at specified inducing exponents. -/
def HasCanonicalEqualNormalization (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (D : ComplexQuotientMeasureData r) (l l' : L) (p p' : P) (Φ : 𝓢(I → ℂ, ℂ)) : Prop :=
  ∀ (f : Std[l, p]) (f' : Std[l', p']),
    let W := continuedJacquet μ (-a) l p f
    let V := continuedJacquet μ a l' p' f'
    HasComplexPairNormalization (characterList l p) (characterList l' p') a
      (complexCentralSign (characterList l' p') ^ r) (complexEqualIntegral D W V Φ)
      (complexEqualDualIntegral a D W V Φ)

/-- The canonical equal-rank pair normalization propagates from a disk about the initial
point of two affine inducing lines to their endpoints at parameter one. -/
def ComplexLocalEqualCanonicalContinuationStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (l l' : L) (p q p' q' : P) (Φ : 𝓢(I → ℂ, ℂ)),
    (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (0 : ℂ) δ,
      HasCanonicalEqualNormalization μ a D l l' (inducingLine p q z) (inducingLine p' q' z) Φ) →
    HasCanonicalEqualNormalization μ a D l l' q q' Φ

set_option maxHeartbeats 650000 in
theorem complexLocalEqualCanonicalContinuation : ComplexLocalEqualCanonicalContinuationStatement (r := r) := by
  intro μ a D l l' p q p' q' Φ h f f'
  let v := transferProfile l q p f
  let v' := transferProfile l' q' p' f'
  let W := canonicalJacquetLine μ (-a) l p q v
  let V := canonicalJacquetLine μ a l' p' q' v'
  let Z (x : ℂ × ℂ) := complexEqualIntegral D (W x.1) (V x.1) Φ x.2
  let Zd (x : ℂ × ℂ) := complexEqualDualIntegral a D (W x.1) (V x.1) Φ x.2
  let c := complexCentralSign (characterList l' q') ^ r
  have hc : c ≠ 0 := pow_ne_zero _ (complexCentralSign_ne_zero _)
  obtain ⟨σ, _, hZ, hZd⟩ := complexLocalEqualCanonicalFamily μ a D l l' p q p' q' v v' Φ 3
  have hSign (z : ℂ) : complexCentralSign (characterList l' (inducingLine p' q' z)) ^ r = c := by
    dsimp only [c]
    rw [complexCentralSign_characterList, complexCentralSign_characterList]
  have hInit : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (0 : ℂ) δ,
      HasComplexPairNormalization (characterList l (inducingLine p q z))
        (characterList l' (inducingLine p' q' z)) a c (fun s => Z (z, s)) (fun s => Zd (z, s)) := by
    obtain ⟨δ, hδ, hδ'⟩ := h
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have h' := hδ' z hz (transferProfile l p (inducingLine p q z) v)
      (transferProfile l' p' (inducingLine p' q' z) v')
    rw [hSign z] at h'
    simpa only [Z, Zd, W, V, canonicalJacquetLine_eq] using h'
  have he := complexPairParameterReflection n n l l' (inducingLine p q) (inducingLine p' q')
    a c hc (differentiable_affine p q) (differentiable_affine p' q') Z Zd σ hZ hZd hInit
  have hW : W 1 = continuedJacquet μ (-a) l q f := by
    calc
      _ = continuedJacquet μ (-a) l (inducingLine p q 1) (transferProfile l p (inducingLine p q 1) v) :=
        canonicalJacquetLine_eq μ (-a) l p q v 1
      _ = continuedJacquet μ (-a) l q (transferProfile l p q v) :=
        congrArg (fun x => continuedJacquet μ (-a) l x (transferProfile l p x v)) (inducingLine_one p q)
      _ = _ := congrArg _ (transferProfile_back l p q f)
  have hV : V 1 = continuedJacquet μ a l' q' f' := by
    calc
      _ = continuedJacquet μ a l' (inducingLine p' q' 1) (transferProfile l' p' (inducingLine p' q' 1) v') :=
        canonicalJacquetLine_eq μ a l' p' q' v' 1
      _ = continuedJacquet μ a l' q' (transferProfile l' p' q' v') :=
        congrArg (fun x => continuedJacquet μ a l' x (transferProfile l' p' x v')) (inducingLine_one p' q')
      _ = _ := congrArg _ (transferProfile_back l' p' q' f')
  simpa only [inducingLine_one, Z, Zd, hW, hV, c] using he

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
