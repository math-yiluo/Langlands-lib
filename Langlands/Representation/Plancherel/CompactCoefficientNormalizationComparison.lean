import Langlands.Representation.Plancherel.CompactCoefficientHaarComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.XiCompactModularComparison

/-! # Change of compact Haar normalization for product-induced coefficients -/

noncomputable section

open MeasureTheory Measure Langlands.Aubert.General
open Langlands.HarishChandraSchwartz
open scoped NNReal TensorProduct

namespace Langlands.Plancherel.CompactInduction

universe uG uV

section Average

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P : Subgroup G} [LocallyCompactSpace P] {K L : Subgroup G} [CompactSpace K] [CompactSpace L]
  {hPK : IsIwasawaPair P K} {hPL : IsIwasawaPair P L} {δ : P →* ℝ≥0ˣ}

/-- The probability Haar average on `K'` of the full Iwasawa weight relative to `L`.
It is the coefficient normalization factor from `L` to `K'`. -/
def coefficientCompactNormalizationScalar (K' : Subgroup G) [CompactSpace K']
    (hPL : IsIwasawaPair P L) (δ : P →* ℝ≥0ˣ) : ℝ :=
  ∫ k : K', iwasawaWeight hPL δ (k : G) ^ 2 ∂normalizedHaar K'

include hPK in
private theorem integral_compact_eq_mul_complex
    (hG : ∀ g : G, modularCharacter g = 1) (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (hδ : ∀ p : P, (δ p : ℝ≥0) = modularCharacter p)
    (hδL : ∀ p : P, (p : G) ∈ L → δ p = 1)
    (φ : G → ℂ) (hφ : Continuous φ)
    (hcov : ∀ (p : P) (x : G), φ ((p : G) * x) = ((δ p : ℝ≥0) : ℝ) * φ x) :
    (∫ k : K, φ k ∂normalizedHaar K) =
      (coefficientCompactNormalizationScalar K hPL δ : ℂ) *
        ∫ l : L, φ l ∂normalizedHaar L := by
  have hKi : Integrable (fun k : K => φ k) (normalizedHaar K) :=
    (hφ.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLi : Integrable (fun l : L => φ l) (normalizedHaar L) :=
    (hφ.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold coefficientCompactNormalizationScalar
  apply Complex.ext
  · have hKr := integral_re hKi
    have hLr := integral_re hLi
    simp only [RCLike.re_eq_complex_re] at hKr hLr
    rw [← hKr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, ← hLr]
    exact integral_compact_eq_mul (hPK := hPK) (hPL := hPL) hG hP hKo hδ hδL
      (fun x => (φ x).re) (Complex.continuous_re.comp hφ) (fun p x => by
        rw [hcov, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero])
  · have hKi' := integral_im hKi
    have hLi' := integral_im hLi
    simp only [RCLike.im_eq_complex_im] at hKi' hLi'
    rw [← hKi', Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, ← hLi']
    exact integral_compact_eq_mul (hPK := hPK) (hPL := hPL) hG hP hKo hδ hδL
      (fun x => (φ x).im) (Complex.continuous_im.comp hφ) (fun p x => by
        rw [hcov, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero])

end Average

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K₁ K₂ : OpenSubgroup G) (hK₁ : IsCompact (K₁ : Set G)) (hK₂ : IsCompact (K₂ : Set G))
  (h₁ : IsIwasawaPair P (K₁ : Subgroup G)) (h₂ : IsIwasawaPair P (K₂ : Subgroup G))
  (hG : ∀ g : G, modularCharacter g = 1)
  (hMod : ∀ p : P, modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))

set_option maxRecDepth 2048 in
/-- The change of compact subgroup multiplies all coefficients on the same
product-induced carrier by one strictly positive scalar, uniform in the
inducing admissible representation and in the evaluation point. -/
theorem exists_pos_coefficientMap_eq_mul_of_compact :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
        (v : productInducedCoefficientObject h hU A) (g : G),
        coefficientMap h hU A K₁ hK₁ hP hm h₁ hG hMod hA v g =
          (c : ℂ) * coefficientMap h hU A K₂ hK₂ hP hm h₂ hG hMod hA v g := by
  let : CompactSpace K₁ := isCompact_iff_compactSpace.mp hK₁
  let : CompactSpace K₂ := isCompact_iff_compactSpace.mp hK₂
  let δ := HaarModulus.closedRestrictCharacter U hU P h.le_normalizer
  have hδ : ∀ p : P, (δ p : ℝ≥0) = modularCharacter p := fun p => (hMod p).symm
  have hδ₂ := modular_eq_one_of_mem hP K₂.isOpen hδ
  let w : K₁ → ℝ := fun k => iwasawaWeight h₂ δ (k : G) ^ 2
  have hw : Continuous w := ((continuous_iwasawaWeight hδ₂ K₂.isOpen (hPK := h₂)).comp
    continuous_subtype_val).pow 2
  have hwpos (k : K₁) : 0 < w k := pow_pos (iwasawaWeight_pos _) _
  refine ⟨coefficientCompactNormalizationScalar (K₁ : Subgroup G) h₂ δ, ?_, ?_⟩
  · change 0 < ∫ k : K₁, w k ∂normalizedHaar (K₁ : Subgroup G)
    rw [integral_pos_iff_support_of_nonneg (fun k => (hwpos k).le)
      (hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have hsupp : Function.support w = Set.univ :=
      Set.eq_univ_of_forall fun k => (hwpos k).ne'
    rw [hsupp, measure_univ]
    exact one_pos
  intro A hA v g
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK₁ h₁
  let E := (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).toLinearEquiv
  let B₁ := coefficientMap h hU A K₁ hK₁ hP hm h₁ hG hMod hA
  let B₂ := coefficientMap h hU A K₂ hK₂ hP hm h₂ hG hMod hA
  let c : ℂ := (coefficientCompactNormalizationScalar (K₁ : Subgroup G) h₂ δ : ℂ)
  change B₁ v g = c * B₂ v g
  obtain ⟨t, rfl⟩ := E.surjective v
  induction t using TensorProduct.inductionOn with
  | tmul f fdual =>
    let φ : G → ℂ := fun x => smoothDualPairing A.representation
      (Induction.eval P (inducingRepresentation h hU A.contragredient) fdual x)
      (Induction.eval P (inducingRepresentation h hU A) f (x * g))
    have hφ : Continuous φ :=
      (Induction.bilinearPairing_isLocallyConstant P _ _ (smoothDualPairing A.representation)
        fdual (((normalizedInductionFunctor h hU).obj A).representation g f)).continuous
    have hcov (p : P) (x : G) : φ ((p : G) * x) = ((δ p : ℝ≥0) : ℝ) * φ x := by
      have ht := Induction.dualPairing_covariant P h.projection
        (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
        A.representation fdual (((normalizedInductionFunctor h hU).obj A).representation g f) p x
      rw [closedHalfCharacter_mul_self h hU p] at ht
      exact ht
    have hchange := integral_compact_eq_mul_complex (hPK := h₁) (hPL := h₂)
      hG hP K₁.isOpen hδ hδ₂ φ hφ hcov
    have hB₁ : B₁ (E (f ⊗ₜ[ℂ] fdual)) g =
        ∫ k : K₁, φ k ∂normalizedHaar (K₁ : Subgroup G) := by
      rw [← measure_eq_normalizedHaar K₁ hK₁]
      exact coefficientMap_tmul h hU A K₁ hK₁ hP hm h₁ hG hMod hA f fdual g
    have hB₂ : B₂ (E (f ⊗ₜ[ℂ] fdual)) g =
        ∫ k : K₂, φ k ∂normalizedHaar (K₂ : Subgroup G) := by
      rw [← measure_eq_normalizedHaar K₂ hK₂]
      exact coefficientMap_tmul h hU A K₂ hK₂ hP hm h₂ hG hMod hA f fdual g
    exact hB₁.trans (hchange.trans (congrArg (c * ·) hB₂.symm))
  | add t₁ t₂ ht₁ ht₂ =>
    have hadd (B : productInducedCoefficientObject h hU A →ₗ[ℂ] LocallyConstant G ℂ) :
        B (E (t₁ + t₂)) g = B (E t₁) g + B (E t₂) g := by
      calc
        _ = B (E t₁ + E t₂) g := congrArg (fun v => B v g) (E.map_add t₁ t₂)
        _ = (B (E t₁) + B (E t₂)) g :=
          congrArg (fun f : LocallyConstant G ℂ => f g) (B.map_add (E t₁) (E t₂))
        _ = _ := rfl
    calc
      _ = B₁ (E t₁) g + B₁ (E t₂) g := hadd B₁
      _ = c * B₂ (E t₁) g + c * B₂ (E t₂) g := congrArg₂ (· + ·) ht₁ ht₂
      _ = c * (B₂ (E t₁) g + B₂ (E t₂) g) := (mul_add _ _ _).symm
      _ = _ := congrArg (c * ·) (hadd B₂).symm

end Langlands.Plancherel.CompactInduction
