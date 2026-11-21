import Langlands.Global.RankinSelberg.ComplexJacquetRegularity
import Langlands.Global.RankinSelberg.ComplexGodementContinuedLie

/-! # The canonical complex Jacquet evaluation is a Whittaker intertwiner -/

noncomputable section
open MeasureTheory Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (matrixModel rightDerivative rightDerivativeLinearMap
  rightDerivative_mem_kFiniteFunctions_complexStandardModule rightDerivative_add rightDerivative_smul
  characterOfParams characterOfParams_exponent characterOfParams_weight)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ComplexCompactProfileFamily (characterList standardSection_mem standardSection_compactRestriction
  compactRestriction compactRestriction_isCompactProfile)
open ComplexGodement (compactGodementSections complexGodementCompactSpanning godementSection
  addedCharacter retainedCharacters smallerWeights smallerExponents smallerSection SmallerProfile characterList_cons
  operatorTestDerivative complexGodementTestDerivative determinantSlope rightDerivative_godementSection
  rightDerivative_continuedValue operatorToEntry_operatorTestDerivative)
open ComplexGodementGeneratorFamily (generatorFamily)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "P" => Fin (r + 1) → ℂ
local notation "L" => Fin (r + 1) → ℤ
local notation "P'" => Fin (r + 1 + 1) → ℂ
local notation "L'" => Fin (r + 1 + 1) → ℤ
local notation "Square" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Square'" => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite (r + 1) (characterList l p)
local notation "Std'[" l "," p "]" => Automorphic.complexStandardKFinite (r + 1 + 1) (characterList l p)

/-- The real right Lie derivative acts complex linearly on the exact compact-finite module. -/
def standardRightDerivative (l : L) (p : P) (X : Square) : Std[l, p] →ₗ[ℂ] Std[l, p] :=
  (rightDerivativeLinearMap (Std[l, p]) (fun _ hf => hf.1.1) X).codRestrict _ fun f =>
    rightDerivative_mem_kFiniteFunctions_complexStandardModule (r + 1) (characterList l p) f.2 X

set_option maxHeartbeats 1600000 in
private theorem continuedJacquet_rightDerivative_succ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : L') (p : P') (X : Square') (f : Std'[l, p]) :
    continuedJacquet μ a l p (standardRightDerivative l p X f) =
      rightDerivative (matrixModel ℂ (r + 1 + 1)) X (continuedJacquet μ a l p f) := by
  let ν := complexGeneralLinearHaar (r + 1)
  let S := compactGodementSections ν (addedCharacter l p) (retainedCharacters l p)
  have hspan : Submodule.span ℂ S = Std'[l, p] := by
    rw [characterList_cons]
    exact complexGodementCompactSpanning ν (addedCharacter l p)
      (fun i => characterOfParams (smallerWeights l i) (smallerExponents p i))
  let lift (g : G' → ℂ) (hg : g ∈ Submodule.span ℂ S) : Std'[l, p] := ⟨g, hspan ▸ hg⟩
  let D := standardRightDerivative l p X
  let J := continuedJacquet μ a l p
  have hSmooth (f : Std'[l, p]) := (complexJacquetRegularity (r + 1) μ a l p f).1
  have hf : f.val ∈ Submodule.span ℂ S := hspan.symm ▸ f.2
  refine Submodule.span_induction (p := fun g hg => J (D (lift g hg)) =
    rightDerivative (matrixModel ℂ (r + 1 + 1)) X (J (lift g hg))) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨Φ, f₀, hΦ, hfull, hfinite, rfl⟩
    let u : SmallerProfile l := ⟨compactRestriction f₀.val, compactRestriction_isCompactProfile f₀.2⟩
    have hu : smallerSection p u = f₀.val := standardSection_compactRestriction f₀.2
    let Ψ := operatorTestDerivative Φ X
    obtain ⟨hΨ, hΨf, hΨfin⟩ := complexGodementTestDerivative Φ X hΦ hfull hfinite
    let v : Std'[l, p] := ⟨godementSection ν (addedCharacter l p) Φ (smallerSection p u),
      godementSection_mem_standardKFinite ν l Φ hΦ hfull hfinite u p⟩
    let v' : Std'[l, p] := ⟨godementSection ν (addedCharacter l p) Ψ (smallerSection p u),
      godementSection_mem_standardKFinite ν l Ψ hΨ hΨf hΨfin u p⟩
    have hv : ∀ hg, lift (godementSection ν (addedCharacter l p) Φ f₀.val) hg = v :=
      fun _ => Subtype.ext (congrArg (godementSection ν (addedCharacter l p) Φ) hu.symm)
    have hm : godementSection ν (addedCharacter l p) Φ f₀.val ∈ S :=
      ⟨Φ, f₀, hΦ, hfull, hfinite, rfl⟩
    rw [hv (Submodule.subset_span hm)]
    let c := determinantSlope (addedCharacter l p) (((r + 1 : ℕ) : ℂ) / 2) X
    have hInput : D v = c • v + v' := by
      apply Subtype.ext
      exact rightDerivative_godementSection ν (addedCharacter l p) Φ hΦ hfull
        (standardSection_mem u.2 (smallerExponents p)).1.1.continuous X
    let W := canonicalJacquetFamily μ a (smallerWeights l) u.val u.2
    have hW := canonicalJacquetFamily_properties μ a (smallerWeights l) u.val u.2
    have hJv : J v = generatorFamily ν μ a l Φ W p :=
      complexJacquetGeneratorEvaluation ν μ a l Φ hΦ hfull hfinite u p
    have hJv' : J v' = generatorFamily ν μ a l Ψ W p :=
      complexJacquetGeneratorEvaluation ν μ a l Ψ hΨ hΨf hΨfin u p
    have hOutput : rightDerivative (matrixModel ℂ (r + 1 + 1)) X (J v) = c • J v + J v' := by
      rw [hJv, hJv']
      unfold generatorFamily
      dsimp only [c, addedCharacter, Ψ]
      rw [operatorToEntry_operatorTestDerivative]
      obtain ⟨δ, hδ, hB⟩ := hW.2.2.1 (smallerExponents p)
      have h := rightDerivative_continuedValue ν μ a (characterOfParams (l 0) 0)
        (Metric.ball (smallerExponents p) δ) W (fun q _ => hW.1 q) hB
        (smallerExponents p) (Metric.mem_ball_self hδ)
        (Langlands.Analysis.SchwartzMatrixNorm.operatorToEntry Φ) (p 0) X
      simpa only [characterOfParams_weight, characterOfParams_exponent, zero_add] using h
    rw [hInput, hOutput, map_add, map_smul]
  · change J (D 0) = rightDerivative (matrixModel ℂ (r + 1 + 1)) X (J 0)
    simp only [map_zero]
    funext g
    simp [rightDerivative, mfderiv_const]
    rfl
  · intro x y hx hy Ex Ey
    change J (D (lift x hx + lift y hy)) =
      rightDerivative (matrixModel ℂ (r + 1 + 1)) X (J (lift x hx + lift y hy))
    simp only [map_add]
    rw [rightDerivative_add (hSmooth _) (hSmooth _) X, Ex, Ey]
  · intro c x hx Ex
    change J (D (c • lift x hx)) = rightDerivative (matrixModel ℂ (r + 1 + 1)) X (J (c • lift x hx))
    simp only [map_smul]
    rw [rightDerivative_smul (hSmooth _) c X, Ex]

/-- The canonical evaluation intertwines the right Lie derivative. -/
theorem continuedJacquet_rightDerivative (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L) (p : P)
    (X : Square) (f f' : Std[l, p]) (h : f'.val = rightDerivative (matrixModel ℂ (r + 1)) X f.val) :
    continuedJacquet μ a l p f' = rightDerivative (matrixModel ℂ (r + 1)) X (continuedJacquet μ a l p f) := by
  cases r with
  | zero => simpa only [continuedJacquet_rankOne] using h
  | succ r =>
    have h' : f' = standardRightDerivative l p X f := Subtype.ext h
    rw [h']
    exact continuedJacquet_rightDerivative_succ μ a l p X f

/-- The entire canonical Jacquet family supplies exact Whittaker intertwiners for every
inducing parameter. -/
def ComplexJacquetIntertwinerStatement : Prop :=
  ∀ (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : Fin (r + 1) → ℤ) (p : Fin (r + 1) → ℂ),
    IsComplexWhittakerIntertwiner r (characterList l p) (-a) (continuedJacquet μ a l p)

theorem complexJacquetIntertwiner : ComplexJacquetIntertwinerStatement := by
  intro r μ a l p
  have hE := complexJacquetEvaluation (r := r) μ a l p
  exact ⟨fun f u hu g => hE.1 f ⟨u, hu⟩ g,
    fun f => (complexJacquetRegularity r μ a l p f).1,
    fun f => (complexJacquetRegularity r μ a l p f).2,
    hE.2.1, fun X f f' h => continuedJacquet_rightDerivative μ a l p X f f' h⟩

/-- The exact Whittaker model contains the canonical evaluation at every inducing parameter. -/
theorem continuedJacquet_mem_complexWhittakerModel (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : L) (p : P) (f : Std[l, p]) : continuedJacquet μ a l p f ∈ complexWhittakerModel r (characterList l p) (-a) :=
  Submodule.mem_iSup_of_mem (continuedJacquet μ a l p)
    (Submodule.mem_iSup_of_mem (complexJacquetIntertwiner r μ a l p) ⟨f, rfl⟩)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
