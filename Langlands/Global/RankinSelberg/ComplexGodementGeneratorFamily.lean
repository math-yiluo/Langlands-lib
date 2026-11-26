import Langlands.Global.RankinSelberg.ComplexGodementFiniteProfiles
import Langlands.Global.RankinSelberg.ComplexGodementRootBounds
import Langlands.Global.RankinSelberg.ComplexJacquetChamberHolomorphic
import Langlands.Analysis.SchwartzMatrixNorm

/-! # Continued Godement generators with uniform Jacquet estimates -/

noncomputable section

open MeasureTheory Set Filter
open scoped Classical Matrix Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementGeneratorFamily

open Langlands.Analysis.SchwartzMatrixNorm (OperatorSchwartz EntrySchwartz operatorToEntry operatorToEntry_apply)
open Langlands.Archimedean (characterOfParams characterOfParams_exponent characterOfParams_weight)
open Langlands.Archimedean.ComplexBlockLanglandsQuotient (complexPositionExponent_ofFn)
open Langlands.Archimedean.ComplexGramFormula (complexPositionExponent)
open Langlands.Archimedean.ComplexPartialJacquet (IsStrictlyDominant)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (extensionLinear)
open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ComplexCompactProfileFamily (characterList IsCompactProfile standardSection standardSection_mem
  standardSection_compactRestriction compactRestriction continuous_standardSection_family differentiable_standardSection)
open ComplexGodement (SmallerProfile smallerWeights smallerExponents addedCharacter retainedCharacters
  smallerSection characterList_cons HasFullRowRank godementSection characterWeight)
open ComplexGodementAddedCharacter (continuedValue rightTest complexGodementAddedCharacterContinuation)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound complexGodementWhittakerFamily)
open ComplexGodementParametric (continuous_continuedValue)
open ComplexGodementRootBounds (HasLeftWhittakerLaw complexGodementRootBounds)
open ComplexJacquetChamberIntertwiner (openCellIntegral_left_mul)
open ComplexJacquetChamberHolomorphic (chamber isOpen_chamber)
open ComplexJacquetUnipotentMeasure (entryHaar)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℂ
local notation "U'" => Matrix.unitaryGroup (Fin (r + 1 + 1)) ℂ
local notation "P" => Fin (r + 1) → ℂ
local notation "P'" => Fin (r + 1 + 1) → ℂ
local notation "L" => Fin (r + 1) → ℤ
local notation "L'" => Fin (r + 1 + 1) → ℤ

theorem isStrictlyDominant_characterList {j : ℕ} (l : Fin (j + 1) → ℤ)
    {p : Fin (j + 1) → ℂ} (hp : p ∈ chamber j) :
    IsStrictlyDominant (complexPositionExponent (characterList l p)) j := by
  intro i hi
  let k : Fin j := ⟨i, hi⟩
  change (complexPositionExponent (characterList l p) k.succ).re <
    (complexPositionExponent (characterList l p) k.castSucc).re
  simpa only [characterList, complexPositionExponent_ofFn, characterOfParams_exponent] using hp k

private theorem smaller_mem_chamber {p : P'} (hp : p ∈ chamber (r + 1)) :
    smallerExponents p ∈ chamber r := by
  intro i
  have h := hp i.succ
  change (p i.succ.succ).re < (p i.succ.castSucc).re at h
  have he : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  rw [he] at h
  exact h

private theorem chamber_nonempty (j : ℕ) : (chamber j).Nonempty := by
  refine ⟨fun i => -((i : ℕ) : ℂ), ?_⟩
  intro i
  change (-((i.succ : ℕ) : ℂ)).re < (-((i.castSucc : ℕ) : ℂ)).re
  simp only [Complex.neg_re, Complex.natCast_re, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one,
    Complex.add_re, Complex.one_re]
  linarith

private def smallerProjection : P' →L[ℂ] P := by
  let T : P' →ₗ[ℂ] P := {
    toFun := smallerExponents
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact T.toContinuousLinearMap

private theorem cont_smallerExponents : Continuous (smallerExponents : P' → P) :=
  (smallerProjection (r := r)).continuous

private theorem diff_smallerExponents : Differentiable ℂ (smallerExponents : P' → P) :=
  (smallerProjection (r := r)).differentiable

private theorem diff_head : Differentiable ℂ (fun p : P' => p 0) :=
  (ContinuousLinearMap.proj 0 : P' →L[ℂ] ℂ).differentiable

private theorem uniform_bound_pullback (W : P → G → ℂ)
    (hWb : ∀ p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball p δ) W) (p : P') :
    ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball p δ) (fun q => W (smallerExponents q)) := by
  obtain ⟨ε, hε, N, hN⟩ := hWb (smallerExponents p)
  have hn : ∀ᶠ q in 𝓝 p, smallerExponents q ∈ Metric.ball (smallerExponents p) ε :=
    cont_smallerExponents.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff_ball.mp hn
  refine ⟨δ, hδ, N, fun J => ?_⟩
  obtain ⟨C, hC, hB⟩ := hN J
  exact ⟨C, hC, fun q hq h => hB (smallerExponents q) (hsub q hq) h⟩

/-- The continued integral for a fixed Schwartz test is pointwise entire in the
inducing parameters under the uniform estimates for the smaller family. -/
theorem differentiable_generatorValue (ν : Measure G) [ν.IsHaarMeasure]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData)
    (Φ : EntrySchwartz (r + 1) (r + 1 + 1)) (W : P → G → ℂ)
    (hWc : ∀ p, Continuous (W p)) (hWd : ∀ h, Differentiable ℂ (fun p => W p h))
    (hWb : ∀ p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball p δ) W) (g : G') :
    Differentiable ℂ (fun p : P' => continuedValue ν μ d a Φ (W (smallerExponents p)) g (p 0)) := by
  let X := rightTest g Φ
  let Ψ := partialSchwartz a μ X
  let t : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2)
  let F (p : P') : G → ℂ := W (smallerExponents p)
  let s (p : P') := t + p 0 - 1
  have hsb := uniform_bound_pullback W hWb
  have hs : Differentiable ℂ s := (diff_head.const_add t).sub_const 1
  have hhol := (complexGodementWhittakerFamily ν Set.univ isOpen_univ d Ψ F s
    (fun p => hWc (smallerExponents p)) (fun h => ((hWd h).comp diff_smallerExponents).differentiableOn)
    (fun p _ => hsb p) hs.differentiableOn).2
  have hIntegral : Differentiable ℂ (fun p : P' =>
      ∫ h, iteratedKernel (complexScaledCharacter a) μ d X (F p) (t + p 0) h ∂ν) := by
    have he (p : P') : iteratedKernel (complexScaledCharacter a) μ d X (F p) (t + p 0) =
        fun h => ComplexGodementWhittaker.kernelBase d Ψ (F p) h *
          ArchimedeanLocal.detPower complexNormalizedAbs h (s p) :=
      funext (iteratedKernel_eq (complexScaledCharacter a) μ d X Ψ (partialSchwartz_apply a μ X) (F p) (t + p 0))
    simp_rw [he]
    exact differentiableOn_univ.mp hhol
  have hg : Differentiable ℂ (fun p : P' => ArchimedeanLocal.detPower complexNormalizedAbs g (p 0)) :=
    (diff_head.mul_const _).cexp
  unfold continuedValue
  exact ((differentiable_const _).mul hg).mul hIntegral

private theorem generatorValue_eq (ν : Measure G) [SFinite ν] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L') (Φ : OperatorSchwartz (r + 1) (r + 1 + 1))
    (hc : HasCompactSupport Φ) (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X) (f : SmallerProfile l)
    (W : P → G → ℂ) (hW : ∀ q ∈ chamber r, ∀ h,
      W q h = openCellIntegral a (entryHaar μ (r + 1)) (standardSection q f.val) h)
    (p : P') (hp : p ∈ chamber (r + 1)) (g : G') :
    continuedValue ν μ (characterOfParams (l 0) 0) a (operatorToEntry Φ) (W (smallerExponents p)) g (p 0) =
      openCellIntegral a (entryHaar μ (r + 1 + 1)) (godementSection ν (addedCharacter l p) Φ (smallerSection p f)) g := by
  let d := characterOfParams (l 0) 0
  let Ψ := operatorToEntry Φ
  have hΨ : (Ψ : Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ → ℂ) = Φ :=
    funext (operatorToEntry_apply Φ)
  have hΨc : HasCompactSupport Ψ := by rw [hΨ]; exact hc
  have hΨfull : ∀ X ∈ tsupport Ψ, HasFullRowRank X := by rw [hΨ]; exact hfull
  have hs := smaller_mem_chamber hp
  have hds : (retainedCharacters l p).length = r + 1 := List.length_ofFn
  have hstrict : IsStrictlyDominant (complexPositionExponent (retainedCharacters l p)) r :=
    isStrictlyDominant_characterList (smallerWeights l) hs
  let f₀ : Automorphic.complexStandardKFinite (r + 1) (retainedCharacters l p) :=
    ⟨smallerSection p f, standardSection_mem f.2 (smallerExponents p)⟩
  have htop : (complexPositionExponent (retainedCharacters l p) 0).re < (d.exponent + p 0).re := by
    let i : Fin (r + 1) := 0
    change (complexPositionExponent (retainedCharacters l p) (i : ℕ)).re < _
    simp only [retainedCharacters, characterList, complexPositionExponent_ofFn, characterOfParams_exponent,
      smallerExponents, d, zero_add]
    exact hp i
  have hW_eq : W (smallerExponents p) = openCellIntegral a (entryHaar μ (r + 1)) f₀.val := funext (hW _ hs)
  have he := (complexGodementAddedCharacterContinuation (r := r) ν μ d (retainedCharacters l p)
    hds hstrict a Ψ hΨc hΨfull f₀ g).2 (p 0) htop
  change continuedValue ν μ d a Ψ (W (smallerExponents p)) g (p 0) = _
  rw [hW_eq, he, hΨ]
  simp only [d, characterOfParams_exponent, characterOfParams_weight, zero_add, addedCharacter, f₀]

/-- Pointwise holomorphic functions on the full parameter space agree everywhere if they
agree on the strict chamber. -/
theorem eq_of_differentiable_eqOn_chamber {j : ℕ} {f g : (Fin (j + 1) → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (he : EqOn f g (chamber j)) : f = g := by
  obtain ⟨p, hp⟩ := chamber_nonempty j
  funext q
  let line (z : ℂ) := p + z • (q - p)
  have hL : Differentiable ℂ line := (differentiable_id.smul_const (q - p)).const_add p
  have hL₀ : line 0 = p := by simp [line]
  have hL₁ : line 1 = q := by simp [line, add_comm p]
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), line z ∈ chamber j := by
    apply hL.continuous.continuousAt.preimage_mem_nhds
    rw [hL₀]
    exact isOpen_chamber.mem_nhds hp
  have hi : (f ∘ line) =ᶠ[𝓝 (0 : ℂ)] (g ∘ line) := hn.mono fun _ hz => he hz
  have h := AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => (hf.comp hL).analyticAt z)
    (fun z _ => (hg.comp hL).analyticAt z) hi
  simpa only [Function.comp_apply, hL₁] using congrFun h 1

/-- A continued Godement generator with fixed angular weights and a smaller Jacquet family. -/
def generatorFamily (ν : Measure G) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L')
    (Φ : OperatorSchwartz (r + 1) (r + 1 + 1)) (W : P → G → ℂ) (p : P') (g : G') : ℂ :=
  continuedValue ν μ (characterOfParams (l 0) 0) a (operatorToEntry Φ) (W (smallerExponents p)) g (p 0)

variable (r) in
/-- The compact full-rank Godement generating test has a pointwise entire continued Whittaker
family with continuous group slices and locally uniform logarithmic simple-root estimates. -/
def ComplexGodementGeneratorFamilyStatement : Prop :=
  ∀ (ν : Measure G) [SFinite ν] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L') (Φ : OperatorSchwartz (r + 1) (r + 1 + 1)),
    HasCompactSupport Φ → (∀ X ∈ tsupport Φ, HasFullRowRank X) →
    ∀ (f : SmallerProfile l) (W : P → G → ℂ), (∀ p, Continuous (W p)) →
      (∀ g, Differentiable ℂ (fun p => W p g)) →
      (∀ p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball p δ) W) →
      (∀ p ∈ chamber r, ∀ g, W p g = openCellIntegral a (entryHaar μ (r + 1)) (standardSection p f.val) g) →
      let F := generatorFamily ν μ a l Φ W
      (∀ g, Differentiable ℂ (fun p => F p g)) ∧ (∀ p, Continuous (F p)) ∧
      HasLeftWhittakerLaw (r := r) Set.univ a F ∧
      (∀ p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (r := r + 1) (Metric.ball p δ) F) ∧
      ∀ p ∈ chamber (r + 1), ∀ g,
        F p g = openCellIntegral a (entryHaar μ (r + 1 + 1))
          (godementSection ν (addedCharacter l p) Φ (smallerSection p f)) g

set_option maxHeartbeats 1100000 in
theorem complexGodementGeneratorFamily : ComplexGodementGeneratorFamilyStatement r := by
  intro ν hνf hν hνr μ a l Φ hΦ hfull f W hWc hWd hWb hW F
  let d := characterOfParams (l 0) 0
  let Ψ := operatorToEntry Φ
  let V (p : P') := W (smallerExponents p)
  have hV (p : P') : Continuous (V p) := hWc (smallerExponents p)
  have hdiff (g : G') : Differentiable ℂ (fun p => F p g) :=
    differentiable_generatorValue ν μ a d Ψ W hWc hWd hWb g
  have hch (p : P') (hp : p ∈ chamber (r + 1)) (g : G') :
      F p g = openCellIntegral a (entryHaar μ (r + 1 + 1)) (godementSection ν (addedCharacter l p) Φ (smallerSection p f)) g :=
    generatorValue_eq ν μ a l Φ hΦ hfull f W hW p hp g
  have hleft : HasLeftWhittakerLaw (r := r) Set.univ a F := by
    intro p _ u hu g
    have h := eq_of_differentiable_eqOn_chamber (hdiff (u * g))
      ((hdiff g).const_mul (complexWhittakerCharacter (r := r + 1) (-a) u)) (by
        intro q hq
        change F q (u * g) = complexWhittakerCharacter (r := r + 1) (-a) u * F q g
        rw [hch q hq (u * g), hch q hq g]
        exact openCellIntegral_left_mul μ a _ ⟨u, hu⟩ g)
    exact congrFun h p
  refine ⟨hdiff, ?_, hleft, ?_, hch⟩
  · intro p
    obtain ⟨δ, hδ, hVb⟩ := uniform_bound_pullback W hWb p
    exact continuous_continuedValue ν μ a d (Metric.ball p δ) V (fun q _ => hV q) hVb
      p (Metric.mem_ball_self hδ) Ψ (p 0)
  · intro p
    obtain ⟨δ, hδ, hVb⟩ := uniform_bound_pullback W hWb p
    let ε := min δ 1
    have hε : 0 < ε := lt_min hδ zero_lt_one
    have hsub : Metric.ball p ε ⊆ Metric.ball p δ := Metric.ball_subset_ball (min_le_left _ _)
    have hB : HasUniformSimpleRootBound (Metric.ball p ε) V := by
      obtain ⟨N, hN⟩ := hVb
      refine ⟨N, fun J => ?_⟩
      obtain ⟨C, hC, hbound⟩ := hN J
      exact ⟨C, hC, fun q hq g => hbound q (hsub hq) g⟩
    let t : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2)
    let T : ℝ := |(t - 1).re| + (‖p‖ + 1)
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hq (q : P') (hq : q ∈ Metric.ball p ε) : |(t + q 0 - 1).re| ≤ T := by
      have hn : ‖q - p‖ ≤ 1 := by
        have h := Metric.mem_ball.mp hq
        rw [dist_eq_norm] at h
        exact h.le.trans (min_le_right _ _)
      have hnorm : ‖q‖ ≤ ‖p‖ + 1 := by
        calc
          ‖q‖ = ‖(q - p) + p‖ := by rw [sub_add_cancel]
          _ ≤ ‖q - p‖ + ‖p‖ := norm_add_le _ _
          _ ≤ ‖p‖ + 1 := by linarith
      rw [show (t + q 0 - 1).re = (t - 1).re + (q 0).re by
        simp only [Complex.sub_re, Complex.add_re]; ring]
      exact (abs_add_le _ _).trans (add_le_add le_rfl
        (((Complex.abs_re_le_norm (q 0)).trans (norm_le_pi_norm q 0)).trans hnorm))
    refine ⟨ε, hε, ?_⟩
    exact complexGodementRootBounds ν μ a d (Metric.ball p ε) V (fun q _ => hV q) hB Ψ (fun q => q 0)
      T hT hq (fun q _ => hleft q (mem_univ _))

end Langlands.Global.RankinSelbergGlobal.ComplexGodementGeneratorFamily
