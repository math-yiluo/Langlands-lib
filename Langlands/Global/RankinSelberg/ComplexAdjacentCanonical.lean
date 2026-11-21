import Langlands.Global.RankinSelberg.ComplexAdjacentCanonicalChamber
import Langlands.Global.RankinSelberg.ComplexUnequalCanonicalReflection

/-! # The normalized adjacent-rank equation at every inducing parameter -/

noncomputable section

open MeasureTheory Metric Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ComplexCompactProfileFamily (characterList)
open ComplexGodement (smallerExponents smallerWeights retainedCharacters)
open ComplexJacquetChamberHolomorphic (chamber isOpen_chamber)
open ComplexJacquetContinuation (HasUnequalCanonicalPairNormalization complexUnequalCanonicalReflection
  HasUnequalCanonicalPairGrowth complexUnequalCanonicalGrowthReflection)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r t : ℕ}
local notation "m" => (r + 1 : ℕ)
local notation "L" => Fin (m + 1) → ℤ
local notation "P" => Fin (m + 1) → ℂ
local notation "Q" => Fin m → ℂ
local notation "H" => Langlands.GeneralLinear m ℂ

private theorem smallerExponents_cons (x : ℂ) (q : Q) : smallerExponents (Fin.cons x q) = q := by
  ext i
  simp only [smallerExponents, Fin.cons_succ]

private theorem cons_mem_chamber (q : Q) (hq : q ∈ chamber r) (x : ℂ) (hx : (q 0).re < x.re) :
    Fin.cons x q ∈ chamber m := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ] using hx
  · simpa only [Fin.castSucc_succ, Fin.cons_succ] using hq j

private theorem canonicalChamberRemoval (A : P → Prop)
    (reflection : ∀ p : ℂ → P, Differentiable ℂ p →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, A (p z)) → A (p 1))
    (hStrong : ∀ q : Q, ∃ M : ℕ, ∀ p : P, smallerExponents p = q → p ∈ chamber m →
      (m : ℝ) + M ≤ (p 0 + (((m : ℂ) + 1) / 2)).re → A p) :
    ∀ p : P, A p := by
  let ρ : ℂ := (((m : ℂ) + 1) / 2)
  have hρ : 0 ≤ ρ.re := by
    simp [ρ]
    positivity
  have hHead (q : Q) (hq : q ∈ chamber r) (x : ℂ) : A (Fin.cons x q) := by
    obtain ⟨M, hM⟩ := hStrong q
    let x₀ : ℂ := (max (q 0).re ((m : ℝ) + M) + 1 : ℝ)
    let u (z : ℂ) := x₀ + z * (x - x₀)
    let p (z : ℂ) : P := Fin.cons (u z) q
    have hu : Differentiable ℂ u := (differentiable_id.mul_const (x - x₀)).const_add x₀
    have hp : Differentiable ℂ p := by
      apply differentiable_pi.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [p, Fin.cons_zero] using hu
      · simpa only [p, Fin.cons_succ] using differentiable_const (q j)
    have hp₁ : p 1 = Fin.cons x q := by simp [p, u, add_comm x₀]
    let S : Set ℂ := {z : ℂ | (q 0).re < (u z).re} ∩
      {z : ℂ | (m : ℝ) + M < (u z + ρ).re}
    have hS : IsOpen S :=
      (isOpen_lt continuous_const (Complex.continuous_re.comp hu.continuous)).inter
        (isOpen_lt continuous_const (Complex.continuous_re.comp (hu.continuous.add continuous_const)))
    have hz₀ : (0 : ℂ) ∈ S := by
      refine ⟨?_, ?_⟩
      · change (q 0).re < (u 0).re
        simp only [u, zero_mul, add_zero, x₀, Complex.ofReal_re]
        linarith [le_max_left (q 0).re ((m : ℝ) + M)]
      · change (m : ℝ) + M < (u 0 + ρ).re
        simp only [u, zero_mul, add_zero, x₀, Complex.add_re, Complex.ofReal_re]
        linarith [le_max_right (q 0).re ((m : ℝ) + M)]
    obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS 0 hz₀
    rw [← hp₁]
    refine reflection p hp ⟨δ, hδ, fun z hz => ?_⟩
    have hzS := hδS hz
    apply hM (p z) (smallerExponents_cons (u z) q) (cons_mem_chamber q hq (u z) hzS.1)
    simpa only [p, Fin.cons_zero] using
      (show (m : ℝ) + M ≤ (u z + ρ).re from le_of_lt hzS.2)
  intro p
  let p₀ : P := fun i => -((i : ℕ) : ℂ)
  have hp₀ : smallerExponents p₀ ∈ chamber r := by
    intro i
    simp only [smallerExponents, p₀, Complex.neg_re, Fin.val_succ, Fin.val_castSucc,
      Nat.cast_succ, Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith
  let pLine (z : ℂ) : P := p₀ + z • (p - p₀)
  have hLine : Differentiable ℂ pLine := (differentiable_id.smul_const (p - p₀)).const_add p₀
  have hLine₁ : pLine 1 = p := by simp [pLine, add_comm p₀]
  have hTail : Continuous (smallerExponents : P → Q) :=
    continuous_pi fun i : Fin m => continuous_apply i.succ
  have hS : IsOpen ((smallerExponents ∘ pLine) ⁻¹' chamber r) :=
    isOpen_chamber.preimage (hTail.comp hLine.continuous)
  have h₀ : (0 : ℂ) ∈ (smallerExponents ∘ pLine) ⁻¹' chamber r := by
    simpa only [mem_preimage, Function.comp_apply, pLine, zero_smul, add_zero] using hp₀
  obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS 0 h₀
  rw [← hLine₁]
  refine reflection pLine hLine ⟨δ, hδ, fun z hz => ?_⟩
  have h := hHead (smallerExponents (pLine z)) (hδS hz) (pLine z 0)
  rw [show smallerExponents (pLine z) = Fin.tail (pLine z) by rfl, Fin.cons_self_tail] at h
  exact h

/-- A head threshold depending on the fixed tail is enough to continue the
unequal-rank normalized equation for all larger inducing exponents. -/
theorem complexUnequalCanonicalFromChamber (h : t < m) (μ : AdditiveHaarMeasure ℂ)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) (l : L) (k : Fin (t + 1) → ℤ) (e : Fin (t + 1) → ℂ)
    (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ) (hV : V ∈ complexWhittakerModel t (characterList k e) a)
    (hStrong : ∀ q : Q, ∃ M : ℕ, ∀ p : P, smallerExponents p = q → p ∈ chamber m →
      (m : ℝ) + M ≤ (p 0 + (((m : ℂ) + 1) / 2)).re →
      HasUnequalCanonicalPairNormalization h μ a D l p (characterList k e) V) :
    ∀ p : P, HasUnequalCanonicalPairNormalization h μ a D l p (characterList k e) V :=
  canonicalChamberRemoval _ (complexUnequalCanonicalReflection h μ a D l k e V hV) hStrong

/-- The strip-growing unequal equation extends from a head threshold to all larger exponents. -/
theorem complexUnequalCanonicalGrowthFromChamber (h : t < m) (μ : AdditiveHaarMeasure ℂ)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) (l : L) (k : Fin (t + 1) → ℤ) (e : Fin (t + 1) → ℂ)
    (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ) (hV : V ∈ complexWhittakerModel t (characterList k e) a)
    (hStrong : ∀ q : Q, ∃ M : ℕ, ∀ p : P, smallerExponents p = q → p ∈ chamber m →
      (m : ℝ) + M ≤ (p 0 + (((m : ℂ) + 1) / 2)).re →
      HasUnequalCanonicalPairGrowth h μ a D l p (characterList k e) V) :
    ∀ p : P, HasUnequalCanonicalPairGrowth h μ a D l p (characterList k e) V :=
  canonicalChamberRemoval _ (complexUnequalCanonicalGrowthReflection h μ a D l k e V hV) hStrong

private theorem quotient_sFinite (D : ComplexQuotientMeasureData r) : SFinite D.measure := by
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : SecondCountableTopology H := e.secondCountableTopology
  let : LocallyCompactSpace H := e.locallyCompactSpace
  have : SigmaCompactSpace (LeftUnipotentQuotient r ℂ) := by
    have hq := QuotientIntegration.leftQuotient_isOpenQuotientMap (GeneralLinear.upperUnipotent m ℂ)
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr hq.surjective]
    exact isSigmaCompact_range hq.continuous
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  infer_instance

/-- The normalized adjacent-rank equation holds for all larger inducing exponents and for every
smaller intertwiner value, given the lower equal-rank inputs for the retained weight tuple. -/
def ComplexAdjacentCanonicalStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (l : L) (k : Fin m → ℤ) (e : Q) (a : ℂˣ),
    (∀ q : Q, HasAdjacentLowerEqualInputs D (characterList (smallerWeights l) q) (characterList k e) a) →
    ∀ (B : Automorphic.complexStandardKFinite m (characterList k e) →ₗ[ℂ] (H → ℂ)),
      IsComplexWhittakerIntertwiner r (characterList k e) a B →
    ∀ v (p : P), HasUnequalCanonicalPairNormalization (Nat.lt_succ_self r) (complexSelfDualMeasure a)
      a D l p (characterList k e) (B v)

theorem complexAdjacentCanonical : ComplexAdjacentCanonicalStatement (r := r) := by
  intro D l k e a hLower B hB v
  let : SFinite D.measure := quotient_sFinite D
  have hV : B v ∈ complexWhittakerModel r (characterList k e) a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  apply complexUnequalCanonicalFromChamber (Nat.lt_succ_self r) (complexSelfDualMeasure a) a D l k e
    (B v) hV
  intro q
  obtain ⟨M, hM⟩ := complexAdjacentCanonicalChamber D l q
  refine ⟨M, fun p hq hp hb => ?_⟩
  have hl : HasAdjacentLowerEqualInputs D (retainedCharacters l p) (characterList k e) a := by
    simpa only [retainedCharacters, hq] using hLower q
  exact hM p hq hp hb a (characterList k e) List.length_ofFn hl B hB v

/-- The adjacent canonical equation with strip growth at every inducing parameter. -/
def ComplexAdjacentCanonicalGrowthStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (l : L) (k : Fin m → ℤ) (e : Q) (a : ℂˣ),
    (∀ q : Q, HasAdjacentLowerEqualGrowthInputs D (characterList (smallerWeights l) q) (characterList k e) a) →
    ∀ (B : Automorphic.complexStandardKFinite m (characterList k e) →ₗ[ℂ] (H → ℂ)),
      IsComplexWhittakerIntertwiner r (characterList k e) a B →
    ∀ v (p : P), HasUnequalCanonicalPairGrowth (Nat.lt_succ_self r) (complexSelfDualMeasure a)
      a D l p (characterList k e) (B v)

theorem complexAdjacentCanonicalGrowth : ComplexAdjacentCanonicalGrowthStatement (r := r) := by
  intro D l k e a hLower B hB v
  let : SFinite D.measure := quotient_sFinite D
  have hV : B v ∈ complexWhittakerModel r (characterList k e) a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  apply complexUnequalCanonicalGrowthFromChamber (Nat.lt_succ_self r) (complexSelfDualMeasure a) a D l k e
    (B v) hV
  intro q
  obtain ⟨M, hM⟩ := complexAdjacentCanonicalChamberGrowth D l q
  refine ⟨M, fun p hq hp hb => ?_⟩
  have hl : HasAdjacentLowerEqualGrowthInputs D (retainedCharacters l p) (characterList k e) a := by
    simpa only [retainedCharacters, hq] using hLower q
  exact hM p hq hp hb a (characterList k e) List.length_ofFn hl B hB v

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
