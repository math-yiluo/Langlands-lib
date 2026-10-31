import Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct

/-!
# Upper-block integrals of full-matrix test functions

For a Schwartz–Bruhat function `Φ` on `(t + 1) × (t + 1)` matrices, the upper-block
integral `Φ^P (A, D) = ∫ B, Φ [[A, B], [0, D]] dB` is Schwartz–Bruhat on
`Mat_{n₀} × Mat_{n₁}` and a finite sum of products. The integral of
`Φ (parabolicPoint z) * U z.1` over the parabolic parameters reduces to a Levi
integral of `Φ^P` with the radical factor `|det a|^(-n₁)`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.GodementJacquet.TwoBlock

open GeneralLinear RankinSelberg HarmonicAnalysis

universe uF uR

section Blocks

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) {R : Type uR} [CommRing R]

/-- The upper block-triangular matrix `[[A, B], [0, D]]` in the block convention `blockEquiv`. -/
def upperBlockMap
    (z : (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) R × Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) R) ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) R :=
  Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks z.1.1 z.2 0 z.1.2)

/-- The diagonal blocks and the upper-right block of a matrix. -/
def upperBlockCoord (X : Matrix (Fin (t + 1)) (Fin (t + 1)) R) :
    (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) R × Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) R) ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R :=
  let Y := Matrix.reindex (blockEquiv h).symm (blockEquiv h).symm X
  ((Y.toBlocks₁₁, Y.toBlocks₂₂), Y.toBlocks₁₂)

theorem upperBlockCoord_upperBlockMap
    (z : (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) R × Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) R) ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    upperBlockCoord h (upperBlockMap h z) = z := by
  obtain ⟨⟨A, D⟩, B⟩ := z
  simp [upperBlockCoord, upperBlockMap]

theorem parabolicPoint_val_eq_upperBlockMap (L : (succBlockShape m h).Levi R)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    (parabolicPoint h (L, x)).val = upperBlockMap h (((L 0).val, (L 1).val), (L 0).val * x) :=
  parabolicPoint_val h L x

variable [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
theorem continuous_upperBlockMap : Continuous (upperBlockMap h (R := R)) := by
  unfold upperBlockMap
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases (blockEquiv h).symm i with a | a <;> rcases (blockEquiv h).symm j with b | b
  · exact (continuous_apply_apply a b).comp (continuous_fst.comp continuous_fst)
  · exact (continuous_apply_apply a b).comp continuous_snd
  · exact continuous_const
  · exact (continuous_apply_apply a b).comp (continuous_snd.comp continuous_fst)

omit [CommRing R] [IsTopologicalRing R] in
theorem continuous_upperBlockCoord : Continuous (upperBlockCoord h (R := R)) := by
  refine ((?_ : Continuous _).prodMk (?_ : Continuous _)).prodMk (?_ : Continuous _)
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inl i)) ((blockEquiv h) (Sum.inl j))
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inr i)) ((blockEquiv h) (Sum.inr j))
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inl i)) ((blockEquiv h) (Sum.inr j))

end Blocks

section Schwartz

variable {K : Type uF} [Field K] [TopologicalSpace K] [T2Space K]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The restriction `((A, D), B) ↦ Φ [[A, B], [0, D]]` of a full-matrix test function. -/
def upperBlockRestriction (Φ : SchwartzBruhat (Matrix (Fin (t + 1)) (Fin (t + 1)) K)) :
    SchwartzBruhat ((Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) K ×
      Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) K) × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :=
  SchwartzBruhat.compLeftInverse Φ (upperBlockMap h) (upperBlockCoord h)
    (continuous_upperBlockMap h) (continuous_upperBlockCoord h) (upperBlockCoord_upperBlockMap h)

@[simp] theorem upperBlockRestriction_apply
    (Φ : SchwartzBruhat (Matrix (Fin (t + 1)) (Fin (t + 1)) K))
    (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) K) (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) K)
    (B : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    upperBlockRestriction h Φ ((A, D), B) =
      Φ (Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B 0 D)) := rfl

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- **Upper-block integral** `Φ^P (A, D) = ∫ B, Φ [[A, B], [0, D]] dB`, as a
Schwartz–Bruhat function on `Mat_{n₀} × Mat_{n₁}`. -/
def upperBlockIntegral (Φ : SchwartzBruhat (Matrix (Fin (t + 1)) (Fin (t + 1)) K))
    (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K)) [IsFiniteMeasureOnCompacts dx] :
    SchwartzBruhat (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) K ×
      Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) K) :=
  SchwartzBruhat.partialIntegral (upperBlockRestriction h Φ) dx

theorem upperBlockIntegral_apply (Φ : SchwartzBruhat (Matrix (Fin (t + 1)) (Fin (t + 1)) K))
    (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K)) [IsFiniteMeasureOnCompacts dx]
    (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) K) (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) K) :
    upperBlockIntegral h Φ dx (A, D) =
      ∫ B, Φ (Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B 0 D)) ∂dx := rfl

/-- The upper-block integral is a finite sum of products of block test functions. -/
theorem exists_upperBlockIntegral_expansion
    (Φ : SchwartzBruhat (Matrix (Fin (t + 1)) (Fin (t + 1)) K))
    (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K)) [IsFiniteMeasureOnCompacts dx] :
    ∃ (N : ℕ) (Ψ₀ : Fin N → SchwartzBruhat (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) K))
      (Ψ₁ : Fin N → SchwartzBruhat (Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) K)),
      ∀ A D, upperBlockIntegral h Φ dx (A, D) = ∑ j, Ψ₀ j A * Ψ₁ j D :=
  SchwartzBruhat.exists_tensor_expansion (upperBlockIntegral h Φ dx)

end Schwartz

section PiTwo

variable {E : Fin 2 → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : ∀ i, Measure (E i))
  [∀ i, SigmaFinite (μ i)]

/-- Products of integrable functions of the two coordinates are integrable. -/
theorem integrable_pi_two_mul {f₀ : E 0 → ℂ} {f₁ : E 1 → ℂ} (h₀ : Integrable f₀ (μ 0))
    (h₁ : Integrable f₁ (μ 1)) :
    Integrable (fun L : ∀ i, E i => f₀ (L 0) * f₁ (L 1)) (Measure.pi μ) := by
  have hmp := measurePreserving_piFinTwo μ
  exact (hmp.integrable_comp_emb (MeasurableEquiv.piFinTwo E).measurableEmbedding
    (g := fun z : E 0 × E 1 => f₀ z.1 * f₁ z.2)).mpr (h₀.mul_prod h₁)

/-- The integral of a product of functions of the two coordinates. -/
theorem integral_pi_two_mul (f₀ : E 0 → ℂ) (f₁ : E 1 → ℂ) :
    ∫ L : ∀ i, E i, f₀ (L 0) * f₁ (L 1) ∂(Measure.pi μ) =
      (∫ a, f₀ a ∂(μ 0)) * ∫ d, f₁ d ∂(μ 1) := by
  rw [← integral_prod_mul, ← (measurePreserving_piFinTwo μ).integral_comp']
  rfl

end PiTwo

section ParabolicIntegral

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

attribute [local instance] glSecondCountable matrixLocallyCompact matrixSecondCountable
  glLocallyCompact

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [dx.IsAddHaarMeasure]

/-- The radical factor `|det a|^(-n₁)` of a Levi element `L = (a, d)`. -/
def radicalWeight (L : (succBlockShape m h).Levi F.Carrier) : ℂ :=
  (((((F.canonicalTopologicalData.determinantNorm (m 0 + 1) (L 0) : ℝ≥0) : ℝ) ^
    (m 1 + 1))⁻¹ : ℝ) : ℂ)

/-- **Parabolic reduction of a full-matrix test function.** If, for every
Schwartz–Bruhat `α` on `Mat_{n₀} × Mat_{n₁}`, the Levi function
`L ↦ α (a, d) * (U L * |det a|^(-n₁))` is integrable, then
`z ↦ Φ (parabolicPoint z) * U z.1` is integrable for the parabolic measure and its
integral is the Levi integral of `Φ^P (a, d) * U L * |det a|^(-n₁)`. -/
theorem integral_testFunction_parabolicPoint
    (Φ : SchwartzBruhat (Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier))
    (U : (succBlockShape m h).Levi F.Carrier → ℂ)
    (hU : AEStronglyMeasurable U (Measure.pi fun i : Fin 2 => generalLinearHaar F.Carrier (m i)))
    (hint : ∀ α : SchwartzBruhat (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier ×
        Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier),
      Integrable (fun L : (succBlockShape m h).Levi F.Carrier =>
          α ((L 0).val, (L 1).val) * (U L * radicalWeight F h L))
        (Measure.pi fun i : Fin 2 => generalLinearHaar F.Carrier (m i))) :
    Integrable (fun z => Φ (parabolicPoint h z).val * U z.1) (parabolicMeasure F h dx) ∧
      ∫ z, Φ (parabolicPoint h z).val * U z.1 ∂(parabolicMeasure F h dx) =
        ∫ L, upperBlockIntegral h Φ dx ((L 0).val, (L 1).val) * (U L * radicalWeight F h L)
          ∂(Measure.pi fun i : Fin 2 => generalLinearHaar F.Carrier (m i)) := by
  set μL := Measure.pi fun i : Fin 2 => generalLinearHaar F.Carrier (m i) with hμL
  obtain ⟨N, α, β, hf⟩ := SchwartzBruhat.exists_tensor_expansion (upperBlockRestriction h Φ)
  -- the integrand as a finite sum
  let T : Fin N → (succBlockShape m h).Levi F.Carrier ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier → ℂ :=
    fun j z => (α j ((z.1 0).val, (z.1 1).val) * U z.1) * β j ((z.1 0).val * z.2)
  have hsum : (fun z => Φ (parabolicPoint h z).val * U z.1) = fun z => ∑ j, T j z := by
    funext z
    obtain ⟨L, x⟩ := z
    have hΦ : Φ (parabolicPoint h (L, x)).val =
        ∑ j, α j ((L 0).val, (L 1).val) * β j ((L 0).val * x) := by
      rw [parabolicPoint_val_eq_upperBlockMap]
      exact hf ((L 0).val, (L 1).val) ((L 0).val * x)
    rw [hΦ, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [T]
    ring
  have hcont_x : Continuous fun z : (succBlockShape m h).Levi F.Carrier ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier => (z.1 0).val * z.2 :=
    (Units.continuous_val.comp ((continuous_apply (0 : Fin 2)).comp continuous_fst)).matrix_mul
      continuous_snd
  have hcont_L : Continuous fun L : (succBlockShape m h).Levi F.Carrier =>
      ((L 0).val, (L 1).val) :=
    (Units.continuous_val.comp (continuous_apply (0 : Fin 2))).prodMk
      (Units.continuous_val.comp (continuous_apply (1 : Fin 2)))
  have hradw (L : (succBlockShape m h).Levi F.Carrier) :
      ‖radicalWeight F h L‖ =
        (((F.canonicalTopologicalData.determinantNorm (m 0 + 1) (L 0) : ℝ≥0) : ℝ) ^
          (m 1 + 1))⁻¹ := by
    rw [radicalWeight, Complex.norm_real, Real.norm_of_nonneg]
    positivity
  have hTint (j : Fin N) : Integrable (T j) (parabolicMeasure F h dx) := by
    have hm : AEStronglyMeasurable (T j) (parabolicMeasure F h dx) :=
      ((((α j).continuous.comp hcont_L).aestronglyMeasurable.mul hU).comp_fst).mul
        ((β j).continuous.comp hcont_x).aestronglyMeasurable
    rw [parabolicMeasure, integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall fun L => ?_, ?_⟩
    · show Integrable (fun y => (α j ((L 0).val, (L 1).val) * U L) * β j ((L 0).val * y)) dx
      exact ((integrable_mul_left_radical_iff F dx (L 0) (β j)).mpr
        ((β j).integrable dx)).const_mul _
    · have he : (fun L : (succBlockShape m h).Levi F.Carrier =>
          ∫ x, ‖T j (L, x)‖ ∂dx) = fun L =>
            ‖α j ((L 0).val, (L 1).val) * (U L * radicalWeight F h L)‖ *
              ∫ y, ‖β j y‖ ∂dx := by
        funext L
        simp only [T, norm_mul]
        rw [integral_const_mul, integral_mul_left_radical F dx (L 0) (fun y => ‖β j y‖),
          hradw, smul_eq_mul]
        ring
      rw [he]
      exact (hint (α j)).norm.mul_const _
  have hTval (j : Fin N) : ∫ z, T j z ∂(parabolicMeasure F h dx) =
      ∫ L, α j ((L 0).val, (L 1).val) * (U L * radicalWeight F h L) * ∫ y, β j y ∂dx ∂μL := by
    rw [parabolicMeasure, integral_prod _ (hTint j)]
    apply integral_congr_ae
    filter_upwards with L
    simp only [T]
    rw [integral_const_mul, integral_mul_left_radical F dx (L 0) (β j), radicalWeight,
      Complex.real_smul]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finsetSum _ fun j _ => hTint j
  · rw [hsum, integral_finsetSum _ fun j _ => hTint j]
    simp only [hTval]
    rw [← integral_finsetSum _ fun j _ => (hint (α j)).mul_const _]
    apply integral_congr_ae
    filter_upwards with L
    rw [upperBlockIntegral_apply]
    have hB : ∀ B, Φ (Matrix.reindex (blockEquiv h) (blockEquiv h)
        (Matrix.fromBlocks (L 0).val B 0 (L 1).val)) =
          ∑ j, α j ((L 0).val, (L 1).val) * β j B := fun B =>
      (upperBlockRestriction_apply h Φ (L 0).val (L 1).val B).symm.trans (hf _ B)
    simp only [hB]
    rw [integral_finsetSum _ fun j _ => ((β j).integrable dx).const_mul _, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
    ring

end ParabolicIntegral

end Langlands.GodementJacquet.TwoBlock
