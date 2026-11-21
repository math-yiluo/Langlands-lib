import Langlands.BaseChange.StrictWeightCharacters
import Mathlib.Basic.Complex.Basic

/-! # Algebraic replacement of regular elementary traces by spherical traces -/

noncomputable section

namespace Langlands.BaseChange

open Classical
open scoped BigOperators

universe u v w t

/-- Natural multiplicities of the characters in a finite Jacquet expansion.
On the base-field side the characters have already been pulled back by the norm. -/
abbrev JacquetWeightMultiplicities (n : ℕ) := WeightCharacter n ℂ →₀ ℕ

/-- Regard Jacquet multiplicities as complex coefficients of a character sum. -/
def JacquetWeightMultiplicities.coefficients {n : ℕ} (m : JacquetWeightMultiplicities n) :
    WeightCharacter n ℂ →₀ ℂ :=
  m.mapRange Nat.cast Nat.cast_zero

variable {n : ℕ} {I : Type*} {S : Type*} {Test : Type*}

/-- The regular elementary traces expand as character sums with a common scalar factor. -/
def HasElementaryTraceExpansion (multiplicities : I → JacquetWeightMultiplicities n)
    (factor : StrictWeight n → ℂ) (trace : I → StrictWeight n → ℂ) : Prop :=
  ∀ i w, trace i w = factor w *
    strictWeightCharacterEvaluation n (multiplicities i).coefficients w

/-- A chosen character for each powered Satake parameter has a fixed multiplicity on spherical
contributors with that parameter and zero multiplicity on the other contributors. -/
def DetectsSphericalContributors (multiplicities : I → JacquetWeightMultiplicities n)
    (label : I → S) (spherical : I → Prop) (selected : S → WeightCharacter n ℂ)
    (count : S → ℕ) : Prop :=
  ∀ i s, multiplicities i (selected s) = if spherical i ∧ label i = s then count s else 0

/-- The spherical traces are given by the common Satake values on spherical contributors.
The base-field trace has already been evaluated on the image under base change. -/
def HasSphericalTraceValues (label : I → S) (spherical : I → Prop) (value : S → Test → ℂ)
    (trace : I → Test → ℂ) : Prop :=
  ∀ i f, trace i f = if spherical i then value (label i) f else 0

variable [Fintype I]

private theorem sum_elementaryTrace_eq (multiplicities : I → JacquetWeightMultiplicities n)
    (factor : StrictWeight n → ℂ) (trace : I → StrictWeight n → ℂ)
    (h : HasElementaryTraceExpansion multiplicities factor trace)
    (a : I → ℂ) (w : StrictWeight n) :
    ∑ i, a i * trace i w =
      factor w * strictWeightCharacterEvaluation n (∑ i, a i • (multiplicities i).coefficients) w :=
  calc
    _ = ∑ i, factor w *
        (a i * strictWeightCharacterEvaluation n (multiplicities i).coefficients w) := by
      exact Finset.sum_congr rfl (fun i _ ↦ by rw [h i w, mul_left_comm])
    _ = _ := by
      simp only [Finset.mul_sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem sum_selectedCoefficient_eq (multiplicities : I → JacquetWeightMultiplicities n)
    (label : I → S) (spherical : I → Prop) (selected : S → WeightCharacter n ℂ)
    (count : S → ℕ)
    (h : DetectsSphericalContributors multiplicities label spherical selected count)
    (a : I → ℂ) (s : S) :
    (∑ i, a i • (multiplicities i).coefficients) (selected s) =
      (count s : ℂ) * ∑ i, if spherical i ∧ label i = s then a i else 0 := by
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, JacquetWeightMultiplicities.coefficients,
    Finsupp.mapRange_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i s]
  by_cases hi : spherical i ∧ label i = s <;> simp [hi, mul_comm]

private theorem sum_sphericalTrace_eq [Fintype S]
    (label : I → S) (spherical : I → Prop) (value : S → Test → ℂ)
    (trace : I → Test → ℂ) (h : HasSphericalTraceValues label spherical value trace)
    (a : I → ℂ) (f : Test) :
    ∑ i, a i * trace i f =
      ∑ s, (∑ i, if spherical i ∧ label i = s then a i else 0) * value s f := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i f]
  by_cases hi : spherical i
  · simp [hi, eq_comm]
  · simp [hi]

/-- Given character expansions and spherical detection on both sides, a finite weighted
identity on regular elementary tests holds on all paired spherical tests. -/
def SphericalTraceReplacementReductionStatement : Prop :=
  ∀ (n : ℕ) (I : Type u) (J : Type v) (S : Type w) (Test : Type t)
    [Fintype I] [Fintype J] [Fintype S]
    (jacquetE : I → JacquetWeightMultiplicities n) (jacquetF : J → JacquetWeightMultiplicities n)
    (labelE : I → S) (labelF : J → S) (sphericalE : I → Prop) (sphericalF : J → Prop)
    (selected : S → WeightCharacter n ℂ) (count : S → ℕ)
    (factor : StrictWeight n → ℂ) (value : S → Test → ℂ)
    (elementaryE : I → StrictWeight n → ℂ) (elementaryF : J → StrictWeight n → ℂ)
    (traceE : I → Test → ℂ) (traceF : J → Test → ℂ) (a : I → ℂ) (b : J → ℂ),
    (∀ w, factor w ≠ 0) → (∀ s, count s ≠ 0) →
    HasElementaryTraceExpansion jacquetE factor elementaryE →
    HasElementaryTraceExpansion jacquetF factor elementaryF →
    DetectsSphericalContributors jacquetE labelE sphericalE selected count →
    DetectsSphericalContributors jacquetF labelF sphericalF selected count →
    HasSphericalTraceValues labelE sphericalE value traceE →
    HasSphericalTraceValues labelF sphericalF value traceF →
    (∀ w, ∑ i, a i * elementaryE i w = ∑ j, b j * elementaryF j w) →
    ∀ f, ∑ i, a i * traceE i f = ∑ j, b j * traceF j f

theorem sphericalTraceReplacementReduction : SphericalTraceReplacementReductionStatement := by
  intro n I J S Test _ _ _ jacquetE jacquetF labelE labelF sphericalE sphericalF
    selected count factor value elementaryE elementaryF traceE traceF a b
    hfactor hcount hexpE hexpF hdetectE hdetectF htraceE htraceF heq f
  have hcoeff : ∑ i, a i • (jacquetE i).coefficients = ∑ j, b j • (jacquetF j).coefficients :=
    strictWeightCharacterCoefficients_eq factor hfactor _ _ (fun w ↦ by
      rw [← sum_elementaryTrace_eq _ _ _ hexpE, ← sum_elementaryTrace_eq _ _ _ hexpF]
      exact heq w)
  have hgroup (s : S) :
      (∑ i, if sphericalE i ∧ labelE i = s then a i else 0) =
        ∑ j, if sphericalF j ∧ labelF j = s then b j else 0 := by
    have h := congrArg (fun m : WeightCharacter n ℂ →₀ ℂ ↦ m (selected s)) hcoeff
    rw [sum_selectedCoefficient_eq _ _ _ _ _ hdetectE,
      sum_selectedCoefficient_eq _ _ _ _ _ hdetectF] at h
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (hcount s)) h
  rw [sum_sphericalTrace_eq _ _ _ _ htraceE, sum_sphericalTrace_eq _ _ _ _ htraceF]
  exact Finset.sum_congr rfl (fun s _ ↦ congrArg (· * value s f) (hgroup s))

end Langlands.BaseChange
