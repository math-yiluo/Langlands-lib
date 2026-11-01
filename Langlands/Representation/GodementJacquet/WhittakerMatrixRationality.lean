import Langlands.Representation.GodementJacquet.WhittakerIwasawaReduction
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Langlands.LocalField.Normalization.Continuity

/-!
# Rationality of full-matrix Whittaker integrals

Given `FiniteFunctionMellinStatement` and convergence on a right half-plane,
the full-matrix integral `∫ Φ(g) W(g) |det g|^(s + t) dg` of a function `W`
with `IsWhittakerLike` has a rational continuation in `q^(-s)`. On a right
half-plane the integral is a finite linear combination of the torus integrals
of `WhittakerTorusMellin`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.GodementJacquet.WhittakerTorus

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear
open RankinSelberg.RationalContinuationLinear
open scoped BigOperators ENNReal

universe uF

/-- Finitely many conditions, each holding on some right half-plane, hold
together on a right half-plane. -/
theorem exists_common_halfPlane {ι : Type*} (S : Finset ι) (P : ι → ℂ → Prop)
    (h : ∀ i ∈ S, ∃ c : ℝ, ∀ s : ℂ, c < s.re → P i s) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re → ∀ i ∈ S, P i s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun s _ i hi => by simp at hi⟩
  | @insert j S hj ih =>
    obtain ⟨a, ha⟩ := h j (Finset.mem_insert_self j S)
    obtain ⟨b, hb⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨max a b, fun s hs i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ha s ((le_max_left a b).trans_lt hs)
    · exact hb s ((le_max_right a b).trans_lt hs) i hi

/-- A finite sum of functions with rational continuations has a rational
continuation. -/
theorem exists_continuation_sum {ι : Type*} {q : ℕ} (S : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ S, ∃ R : RationalFunctions, HasRationalContinuation q (f i) R) :
    ∃ R : RationalFunctions, HasRationalContinuation q (fun s => ∑ i ∈ S, f i s) R := by
  classical
  choose! R hR using h
  exact ⟨_, continuation_sum S f R hR⟩

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixRationalityTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance matrixRationalityValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance matrixRationalityLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance matrixRationalityUnitsMeasurableSpace : MeasurableSpace F.Carrierˣ := borel _
local instance matrixRationalityUnitsBorelSpace : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance matrixRationalityMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance matrixRationalityBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance matrixRationalityUnipotentMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance matrixRationalityUnipotentBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- The normalized absolute value of a unit is positive. -/
theorem normalizedAbs_units_pos (x : F.Carrierˣ) :
    0 < F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) :=
  (normalizedAbsoluteValue F.canonicalTopologicalData).pos x.ne_zero

/-- `|∏ a_i|` is positive. -/
theorem normalizedAbs_prod_pos (a : Fin (n + 1) → F.Carrierˣ) :
    0 < F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) :=
  (normalizedAbsoluteValue F.canonicalTopologicalData).pos
    (Finset.prod_ne_zero_iff.2 fun i _ => (a i).ne_zero)

/-- `|∏ a_i|` is multiplicative in `a`. -/
theorem normalizedAbs_prod_mul (b a : Fin (n + 1) → F.Carrierˣ) :
    F.canonicalTopologicalData.normalizedAbs (∏ i, ((b * a) i : F.Carrier)) =
      F.canonicalTopologicalData.normalizedAbs (∏ i, (b i : F.Carrier)) *
        F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) := by
  change normalizedAbsoluteValue F.canonicalTopologicalData _ =
    normalizedAbsoluteValue F.canonicalTopologicalData _ *
      normalizedAbsoluteValue F.canonicalTopologicalData _
  rw [← map_mul, ← Finset.prod_mul_distrib]
  simp only [Pi.mul_apply, Units.val_mul]

/-- `a ↦ |∏ a_i|` is continuous. -/
theorem continuous_normalizedAbs_prod :
    Continuous fun a : Fin (n + 1) → F.Carrierˣ =>
      F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) :=
  (PadicField.TopologicalData.continuous_normalizedAbs F.canonicalTopologicalData).comp
    (continuous_finsetProd _ fun i _ => Units.continuous_val.comp (continuous_apply i))

/-- The modulus `δ` is positive. -/
theorem borelModulus_pos (a : Fin (n + 1) → F.Carrierˣ) : 0 < borelModulus F a :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => normalizedAbs_units_pos F _

/-- The modulus `δ` is multiplicative. -/
theorem borelModulus_mul (b a : Fin (n + 1) → F.Carrierˣ) :
    borelModulus F (b * a) = borelModulus F b * borelModulus F a := by
  unfold borelModulus
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  change normalizedAbsoluteValue F.canonicalTopologicalData _ =
    normalizedAbsoluteValue F.canonicalTopologicalData _ *
      normalizedAbsoluteValue F.canonicalTopologicalData _
  rw [← map_mul, ← Units.val_mul, Pi.mul_apply, Pi.mul_apply,
    mul_div_mul_comm (b i) (a i) (b j) (a j)]

/-- The modulus `δ` is continuous. -/
theorem continuous_borelModulus : Continuous (borelModulus F (n := n)) :=
  continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ =>
    (PadicField.TopologicalData.continuous_normalizedAbs F.canonicalTopologicalData).comp
      (Units.continuous_val.comp ((continuous_apply i).div' (continuous_apply j)))

/-- The function `χ(a) δ(a)⁻¹ |∏ a_i|^t` on the torus. -/
def twistedCharacter (χ : (Fin (n + 1) → F.Carrierˣ) → ℂ) (t : ℂ)
    (a : Fin (n + 1) → F.Carrierˣ) : ℂ :=
  χ a * (((borelModulus F a)⁻¹ : ℝ) : ℂ) *
    ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ t

/-- `χ δ⁻¹ |det|^t` is a finite function when `χ` is. -/
theorem isFiniteFunction_twistedCharacter {χ : (Fin (n + 1) → F.Carrierˣ) → ℂ}
    (hχ : IsFiniteFunction χ) (t : ℂ) : IsFiniteFunction (twistedCharacter F χ t) := by
  have hδ : IsFiniteFunction fun a : Fin (n + 1) → F.Carrierˣ =>
      (((borelModulus F a)⁻¹ : ℝ) : ℂ) :=
    IsFiniteFunction.of_mul_apply
      (Complex.continuous_ofReal.comp
        ((continuous_borelModulus F).inv₀ fun a => (borelModulus_pos F a).ne'))
      (fun b => (((borelModulus F b)⁻¹ : ℝ) : ℂ))
      (fun b a => by rw [borelModulus_mul, mul_inv, Complex.ofReal_mul])
  have hdet : IsFiniteFunction fun a : Fin (n + 1) → F.Carrierˣ =>
      ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ t :=
    IsFiniteFunction.of_mul_apply
      ((Complex.continuous_ofReal.comp (continuous_normalizedAbs_prod F)).cpow continuous_const
        fun a => Complex.ofReal_mem_slitPlane.2 (normalizedAbs_prod_pos F a))
      (fun b => ((F.canonicalTopologicalData.normalizedAbs (∏ i, (b i : F.Carrier)) : ℝ) : ℂ) ^ t)
      (fun b a => by
        rw [normalizedAbs_prod_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (normalizedAbs_prod_pos F b).le
            (normalizedAbs_prod_pos F a).le])
  exact (hχ.mul hδ).mul hdet

/-- The slice integral of `Φ(· k)`, as a Schwartz–Bruhat function on `F^(n+1)`. -/
def sliceTest (ψ : UnitaryAdditiveCharacter F.Carrier) (Φ : MatrixTestFunction n F.Carrier)
    (k : Langlands.GeneralLinear (n + 1) F.Carrier) :
    SchwartzBruhat (Fin (n + 1) → F.Carrier) :=
  ⟨_, WhittakerSlice.sliceIntegral_rightTranslate_mem ψ Φ k⟩

theorem sliceTest_apply (ψ : UnitaryAdditiveCharacter F.Carrier)
    (Φ : MatrixTestFunction n F.Carrier) (k : Langlands.GeneralLinear (n + 1) F.Carrier)
    (x : Fin (n + 1) → F.Carrier) :
    sliceTest F ψ Φ k x = WhittakerSlice.sliceIntegral F ψ (fun M => Φ (M * k.val)) x :=
  rfl

/-- **Rationality of full-matrix Whittaker integrals.** Assume
`FiniteFunctionMellinStatement`, and let `W` satisfy `IsWhittakerLike`. If
`∫ Φ(g) W(g) |det g|^s dg` converges absolutely on a right half-plane, then for
every `t` the function `s ↦ ∫ Φ(g) W(g) |det g|^(s + t) dg` has a rational
continuation in `q^(-s)`. -/
theorem IsWhittakerLike.hasRationalContinuation (hFFM : FiniteFunctionMellinStatement.{uF})
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F.Carrier) (t : ℂ)
    (hconv : ∃ c : ℝ, ∀ s : ℂ, c < s.re → GodementJacquet.Padic.MatrixConverges F Φ s W) :
    ∃ R : RationalFunctions,
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (fun s => GodementJacquet.Padic.matrixIntegral F Φ (s + t) W) R := by
  classical
  obtain ⟨K₀, S, -, hSK, hinv, -, hsum⟩ := hW.exists_cosetSum F Φ
  have hexp : ∀ k : Langlands.GeneralLinear (n + 1) F.Carrier,
      ∃ X : Finset ((Fin (n + 1) → F.Carrierˣ) → ℂ), (∀ χ ∈ X, IsFiniteFunction χ) ∧
        ∃ φ : ((Fin (n + 1) → F.Carrierˣ) → ℂ) → SchwartzBruhat (Fin n → F.Carrier),
          ∀ a, W (Iwasawa.diagonalUnits a * k) = ∑ χ ∈ X, φ χ (ratios F a) * χ a :=
    hW.expansion
  choose X hX φ hφ using hexp
  have hM : ∀ k, ∀ χ ∈ X k,
      (∃ c : ℝ, ∀ s : ℂ, c < s.re →
        Integrable (torusIntegrand F (φ k χ) (sliceTest F ψ Φ k) (twistedCharacter F χ t) s)
          (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier)) ∧
      ∃ R : RationalFunctions,
        HasRationalContinuation F.canonicalTopologicalData.residueCardinality
          (fun s => ∫ a, torusIntegrand F (φ k χ) (sliceTest F ψ Φ k)
              (twistedCharacter F χ t) s a
            ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) R :=
    fun k χ hχ => torusMellin F hFFM _ (isFiniteFunction_twistedCharacter F (hX k χ hχ) t)
      (φ k χ) (sliceTest F ψ Φ k)
  obtain ⟨c₀, hc₀⟩ := hconv
  obtain ⟨c₁, hc₁⟩ := exists_common_halfPlane S _ fun k _ =>
    exists_common_halfPlane (X k) _ fun χ hχ => (hM k χ hχ).1
  have key : ∀ s : ℂ, c₀ - t.re < s.re → c₁ < s.re →
      GodementJacquet.Padic.matrixIntegral F Φ (s + t) W =
        ∑ k ∈ S, ((generalLinearHaar F.Carrier n).real
            (K₀ : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂ) *
          ∑ χ ∈ X k, ∫ a, torusIntegrand F (φ k χ) (sliceTest F ψ Φ k)
              (twistedCharacter F χ t) s a
            ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier := by
    intro s hs₀ hs₁
    have hI : Integrable (GodementJacquet.Padic.matrixIntegrand F Φ (s + t) W)
        (generalLinearHaar F.Carrier n) :=
      hc₀ (s + t) (by rw [Complex.add_re]; linarith)
    change ∫ g, GodementJacquet.Padic.matrixIntegrand F Φ (s + t) W g
      ∂generalLinearHaar F.Carrier n = _
    rw [integral_iwasawa F _ hI]
    refine (hsum _ ?_).trans ?_
    · intro k _ k₀ hk₀
      simp_rw [← mul_assoc _ k k₀, fun g => hinv (s + t) g k₀ hk₀]
    · refine Finset.sum_congr rfl fun k hk => ?_
      congr 1
      rw [← integral_finsetSum (X k) fun χ hχ => hc₁ s hs₁ k hk χ hχ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      have hne : ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) :
          ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (normalizedAbs_prod_pos F a).ne'
      simp only []
      rw [integral_unipotent_matrixIntegrand F hW.equivariant Φ (s + t) a (hSK hk), hφ k a,
        Complex.cpow_add _ _ hne]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      simp only [torusIntegrand, twistedCharacter, sliceTest_apply]
      ring
  have hrat : ∃ R : RationalFunctions,
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (fun s => ∑ k ∈ S, ((generalLinearHaar F.Carrier n).real
            (K₀ : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂ) *
          ∑ χ ∈ X k, ∫ a, torusIntegrand F (φ k χ) (sliceTest F ψ Φ k)
              (twistedCharacter F χ t) s a
            ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) R := by
    refine exists_continuation_sum S _ fun k _ => ?_
    obtain ⟨R, hR⟩ := exists_continuation_sum (X k) _ fun χ hχ => (hM k χ hχ).2
    exact ⟨_, hasRationalContinuation_const_mul _ hR⟩
  obtain ⟨R, hR⟩ := hrat
  exact ⟨R, continuation_of_eq_on_right hR ⟨max (c₀ - t.re) c₁, fun s hs =>
    key s ((le_max_left _ _).trans_lt hs) ((le_max_right _ _).trans_lt hs)⟩⟩

end Padic

end Langlands.GodementJacquet.WhittakerTorus
