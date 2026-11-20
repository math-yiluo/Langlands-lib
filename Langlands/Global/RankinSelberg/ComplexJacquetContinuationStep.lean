import Langlands.Analysis.HolomorphicLinearContinuation
import Langlands.Analysis.SchwartzMatrixNorm
import Langlands.Global.RankinSelberg.ComplexGodementAddedCharacter
import Langlands.Global.RankinSelberg.ComplexGodementCompactHolomorphic
import Langlands.Global.RankinSelberg.ComplexGodementFiniteProfiles
import Langlands.Global.RankinSelberg.ComplexGodementWhittakerFamily
import Langlands.Global.RankinSelberg.ComplexJacquetChamberHolomorphic
import Langlands.Representation.Archimedean.RealInductionStagesFamily
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # The pointwise holomorphic Jacquet continuation step -/

noncomputable section

open MeasureTheory Set Filter
open scoped Classical Matrix Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

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

private theorem isStrictlyDominant_characterList {j : ℕ} (l : Fin (j + 1) → ℤ)
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

/-- The smaller-rank hypothesis for one Godement continuation step. Each admissible compact
profile has a jointly holomorphic continuation at fixed group argument with locally uniform
simple-root bounds and continuous group slices. -/
def HasLocallyUniformJacquetFamily (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) : Prop :=
  ∀ (l : Fin (r + 1) → ℤ) (φ : Matrix.unitaryGroup (Fin (r + 1)) ℂ → ℂ), IsCompactProfile l φ →
    ∃ W : (Fin (r + 1) → ℂ) → Langlands.GeneralLinear (r + 1) ℂ → ℂ,
      (∀ p, Continuous (W p)) ∧ (∀ g, Differentiable ℂ (fun p => W p g)) ∧
      (∀ p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball p δ) W) ∧
      ∀ p ∈ chamber r, ∀ g, W p g = openCellIntegral a (entryHaar μ (r + 1)) (standardSection p φ) g

private theorem differentiable_generatorValue (ν : Measure G) [ν.IsHaarMeasure]
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
  have hsb (p : P') : ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball p δ) F := by
    obtain ⟨ε, hε, N, hN⟩ := hWb (smallerExponents p)
    have hn : ∀ᶠ q in 𝓝 p, smallerExponents q ∈ Metric.ball (smallerExponents p) ε :=
      cont_smallerExponents.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff_ball.mp hn
    refine ⟨δ, hδ, N, fun J => ?_⟩
    obtain ⟨C, hC, hB⟩ := hN J
    exact ⟨C, hC, fun q hq h => hB (smallerExponents q) (hsub q hq) h⟩
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

private theorem det_ne_zero_of_spanning {k : ℕ} {J : Type*} (v : J → Fin k → ℂ)
    (hv : Submodule.span ℂ (range v) = ⊤) :
    ∃ b : Fin k → J, Matrix.det (fun i j => v (b i) j) ≠ 0 := by
  have hdim : Module.finrank ℂ (Submodule.span ℂ (range v)) = k := by
    rw [hv, finrank_top, Module.finrank_fin_fun]
  have h := Submodule.exists_fun_fin_finrank_span_eq ℂ (range v)
  rw [hdim] at h
  obtain ⟨f, hf, _, hfi⟩ := h
  choose b hb using hf
  refine ⟨b, (?_ : IsUnit (Matrix.det (fun i j => v (b i) j))).ne_zero⟩
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  have he : Matrix.row (fun i j => v (b i) j) = f := funext hb
  rw [he]
  exact hfi

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

private def chamberEvaluation (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L') (p : P')
    (hp : p ∈ chamber (r + 1)) (A : Submodule ℂ (U' → ℂ)) (hA : ∀ v : A, IsCompactProfile l v.val)
    (g : G') : A →ₗ[ℂ] ℂ := by
  let lift : A →ₗ[ℂ] (G' → ℂ) := {
    toFun := fun f => standardSection p f.val
    map_add' := fun x y => (extensionLinear _).map_add x.val y.val
    map_smul' := fun c x => (extensionLinear _).map_smul c x.val }
  let D := lift.codRestrict (Automorphic.complexStandardKFinite (r + 1 + 1) (characterList l p))
    (fun v => standardSection_mem (hA v) p)
  exact (LinearMap.proj (R := ℂ) g).comp
    ((ComplexJacquetChamberIntertwiner.chamberIntertwiner μ (characterList l p) a
      (isStrictlyDominant_characterList l hp)).comp D)

private theorem dotProduct_evaluation {Q : Type*} [AddCommGroup Q] [Module ℂ Q] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ Q) (ℓ : Q →ₗ[ℂ] ℂ) (v : Q) :
    b.equivFun v ⬝ᵥ (fun i => ℓ (b i)) = ℓ v := by
  unfold dotProduct
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.equivFun_apply]

variable (r) in
/-- A locally uniformly bounded entire smaller-rank Jacquet family gives an entire
continuation of every larger-rank fixed-profile Jacquet value at each fixed group argument. -/
def ComplexJacquetContinuationStepStatement : Prop :=
  ∀ (ν : Measure G) [SFinite ν] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ), HasLocallyUniformJacquetFamily r μ a →
    ∀ (l : L') (φ : U' → ℂ), IsCompactProfile l φ →
      ∃ W : P' → G' → ℂ,
        (∀ g, Differentiable ℂ (fun p => W p g)) ∧
        ∀ p ∈ chamber (r + 1), ∀ g,
          W p g = openCellIntegral a (entryHaar μ (r + 1 + 1)) (standardSection p φ) g

set_option maxHeartbeats 1800000 in
theorem complexJacquetContinuationStep : ComplexJacquetContinuationStepStatement r := by
  intro ν hνf hν hνr μ a hLower l φ hφ
  obtain ⟨A, hAfin, hφA, hA, J, Φ, f, htest, hspan⟩ :=
    ComplexGodement.complexGodementFiniteProfiles ν l φ hφ
  choose W hW using fun j : J => hLower (smallerWeights l) (f j).val (f j).2
  let b := Module.finBasis ℂ A
  let φA : A := ⟨φ, hφA⟩
  let gen (j : J) (p : P') := godementSection ν (addedCharacter l p) (Φ j) (smallerSection p (f j))
  let v (j : J) (p : P') : A := ⟨compactRestriction (gen j p), by
    rw [← hspan p]
    exact Submodule.subset_span ⟨j, rfl⟩⟩
  let u (j : J) (p : P') := b.equivFun (v j p)
  have hgen (j : J) (g : G') : Differentiable ℂ (fun p => gen j p g) := by
    have hfc := (continuous_standardSection_family (f j).2.1).comp
      ((cont_smallerExponents.comp continuous_fst).prodMk continuous_snd)
    have hfd (h : G) := (differentiable_standardSection (f j).val h).comp diff_smallerExponents
    exact ComplexGodement.complexGodementCompactHolomorphic ν (l 0) _ diff_head (Φ j)
      (Φ j).continuous (htest j).1 (htest j).2.1 (fun p => smallerSection p (f j)) hfc hfd g
  have hu (j : J) (i : Fin (Module.finrank ℂ A)) : Differentiable ℂ (fun p => u j p i) := by
    obtain ⟨k, x, c, hx⟩ := Langlands.Archimedean.InductionStages.exists_eval_sum A (b.coord i)
    have he : (fun p => u j p i) = fun p => ∑ t : Fin k, c t * gen j p (Unitary.toUnits (x t)) := by
      funext p
      exact hx (v j p)
    rw [he]
    exact Differentiable.fun_sum fun t _ => (hgen j (Unitary.toUnits (x t))).const_mul _
  have huSpan (p : P') : Submodule.span ℂ (range fun j => u j p) = ⊤ := by
    let S := Submodule.span ℂ (range fun j => v j p)
    have hmap : S.map A.subtype = A := by
      change (Submodule.span ℂ (range fun j => v j p)).map A.subtype = A
      rw [Submodule.map_span, ← Set.range_comp]
      exact hspan p
    have hS : S = ⊤ := by
      apply Submodule.map_injective_of_injective A.injective_subtype
      rw [hmap, Submodule.map_top, Submodule.range_subtype]
    have h := congrArg (fun T : Submodule ℂ A => T.map b.equivFun.toLinearMap) hS
    change (Submodule.span ℂ (range fun j => v j p)).map b.equivFun.toLinearMap =
      (⊤ : Submodule ℂ A).map b.equivFun.toLinearMap at h
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr b.equivFun.surjective] at h
    exact h
  have hStd (j : J) (p : P') : gen j p ∈ Automorphic.complexStandardKFinite (r + 1 + 1) (characterList l p) := by
    rw [characterList_cons]
    exact ComplexGodement.complexGodementKFinite (r + 1) ν (addedCharacter l p) (retainedCharacters l p)
      (Φ j) ((Φ j).smooth ⊤) (htest j).1 (htest j).2.1 (htest j).2.2 (smallerSection p (f j))
      (standardSection_mem (f j).2 (smallerExponents p)).1
  have hAt (g : G') : ∃ F : P' → ℂ, Differentiable ℂ F ∧ ∀ p ∈ chamber (r + 1),
      F p = openCellIntegral a (entryHaar μ (r + 1 + 1)) (standardSection p φ) g := by
    let value (j : J) (p : P') :=
      continuedValue ν μ (characterOfParams (l 0) 0) a (operatorToEntry (Φ j))
        (W j (smallerExponents p)) g (p 0)
    have hvalue (j : J) : Differentiable ℂ (value j) :=
      differentiable_generatorValue ν μ a _ (operatorToEntry (Φ j)) (W j) (hW j).1 (hW j).2.1 (hW j).2.2.1 g
    let c₀ (p : P') (i : Fin (Module.finrank ℂ A)) :=
      openCellIntegral a (entryHaar μ (r + 1 + 1)) (standardSection p (b i).val) g
    have hseed (p : P') (hp : p ∈ chamber (r + 1)) (j : J) : u j p ⬝ᵥ c₀ p = value j p := by
      let ℓ := chamberEvaluation μ a l p hp A hA g
      change b.equivFun (v j p) ⬝ᵥ (fun i => ℓ (b i)) = value j p
      rw [dotProduct_evaluation]
      change openCellIntegral a (entryHaar μ (r + 1 + 1)) (standardSection p (compactRestriction (gen j p))) g =
        value j p
      rw [standardSection_compactRestriction (hStd j p)]
      exact (generatorValue_eq ν μ a l (Φ j) (htest j).1 (htest j).2.1 (f j) (W j) (hW j).2.2.2 p hp g).symm
    obtain ⟨c, hcd, _, hc⟩ := Langlands.Analysis.holomorphicLinearContinuation u value hu hvalue
      (fun p => det_ne_zero_of_spanning _ (huSpan p)) (chamber (r + 1)) isOpen_chamber
      (chamber_nonempty (r + 1)) c₀ hseed
    refine ⟨fun p => b.equivFun φA ⬝ᵥ c p, Differentiable.fun_sum (fun i _ => (hcd i).const_mul _), ?_⟩
    intro p hp
    change b.equivFun φA ⬝ᵥ c p = _
    rw [hc hp]
    exact dotProduct_evaluation b (chamberEvaluation μ a l p hp A hA g) φA
  choose F hF using hAt
  exact ⟨fun p g => F g p, fun g => (hF g).1, fun p hp g => (hF g).2 p hp⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
