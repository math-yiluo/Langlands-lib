import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeftHaarSquareIntegrableUnitarity

/-! # Unitarity from square-integrable coefficients on the supplied central quotient -/

noncomputable section

universe u uV

open MeasureTheory MeasureTheory.Measure
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

open Plancherel

namespace LeftHaarQuotientDualForm

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (C : Subgroup H) [C.Normal] (hC : C ≤ Subgroup.center H)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
  [MeasurableSpace (H ⧸ C)] (measure : Measure (H ⧸ C)) [measure.IsHaarMeasure]

private theorem integral_mul_left_of_continuous {Q : Type*} [Group Q] [TopologicalSpace Q]
    [MeasurableSpace Q] (ν : Measure Q) [ν.IsHaarMeasure] (g : Q) (f : Q → ℂ)
    (hf : Continuous f) (hm : AEStronglyMeasurable f ν) :
    (∫ q, f (g * q) ∂ν) = ∫ q, f q ∂ν := by
  have hmap : ν.map (g * ·) = ν := map_mul_left_eq_self ν g
  by_cases hg : AEMeasurable (g * ·) ν
  · exact (integral_map hg (hmap.symm ▸ hm)).symm.trans (by rw [hmap])
  · -- In Mathlib's total measure map this branch is supported by a Dirac measure.
    have hν : ν ≠ 0 := by
      intro h
      exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne' (by simp [h])
    have hdirac : ν = dirac (Classical.ofNonempty : Q) :=
      hmap.symm.trans (map_of_not_aemeasurable_of_ne_zero hg hν)
    let k := hm.aemeasurable.mk f (Classical.ofNonempty : Q)
    have hkDirac : hm.aemeasurable.mk f =ᵐ[dirac (Classical.ofNonempty : Q)]
        Function.const Q k := ae_eq_dirac' hm.aemeasurable.measurable_mk
    have hk : f =ᵐ[ν] Function.const Q k := by
      refine hm.aemeasurable.ae_eq_mk.trans ?_
      exact Eq.mpr (congrArg (fun m => hm.aemeasurable.mk f =ᵐ[m] Function.const Q k)
        hdirac) hkDirac
    have hconst : f = Function.const Q k := eq_of_ae_eq hk hf continuous_const
    simp only [hconst, Function.const_apply]

-- Polarization gives measurability of the coefficient pair on the given quotient.
omit [IsTopologicalGroup H] [measure.IsHaarMeasure] in
private theorem integrableCoefficientPair (c : UnitaryCentralCharacter ρ)
    (hc : ∀ (ℓ : SmoothDual ρ) (x : V),
      MemLp (centralSubgroupCoefficientNorm C hC c ℓ.val x) 2 measure)
    (x : V) (ℓ₁ ℓ₂ : SmoothDual ρ) :
    Integrable (LeftHaarDualForm.integrand C hC c x ℓ₁ ℓ₂) measure := by
  let square (ℓ : SmoothDual ρ) (q : H ⧸ C) : ℂ :=
    (centralSubgroupCoefficientNorm C hC c ℓ.val x q : ℂ) ^ 2
  have hsquare (ℓ : SmoothDual ρ) : Integrable (square ℓ) measure := by
    simpa only [square, pow_two, ← Complex.ofReal_mul, Pi.mul_apply,
      RCLike.ofReal_eq_complex_ofReal] using
      (((hc ℓ x).integrable_mul (hc ℓ x)).ofReal (𝕜 := ℂ))
  have heq : LeftHaarDualForm.integrand C hC c x ℓ₁ ℓ₂ = fun q =>
      (square (ℓ₂ + ℓ₁) q - square (ℓ₂ - ℓ₁) q +
        (square (ℓ₂ - Complex.I • ℓ₁) q - square (ℓ₂ + Complex.I • ℓ₁) q) *
          Complex.I) / 4 := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simpa [square, matrixCoefficient, RCLike.inner_apply, RCLike.I_to_complex] using
      (inner_eq_sum_norm_sq_div_four (𝕜 := ℂ)
        (ℓ₂.val (ρ g x)) (ℓ₁.val (ρ g x)))
  rw [heq]
  exact (((hsquare _).sub (hsquare _)).add
    (((hsquare _).sub (hsquare _)).mul_const Complex.I)).div_const 4

/-- The integrated coefficient form on the smooth dual for a vector with a spanning orbit. -/
def positiveForm (hρ : IsSmooth ρ) (c : UnitaryCentralCharacter ρ)
    (hc : ∀ (ℓ : SmoothDual ρ) (v : V),
      MemLp (centralSubgroupCoefficientNorm C hC c ℓ.val v) 2 measure)
    (x : V) (hspan : Submodule.span ℂ (Set.range fun g : H => ρ g x) = ⊤) :
    InvariantPositiveForm (smoothContragredient ρ) := by
  let B := LeftHaarDualForm.form C hC measure c x
  have hpair := integrableCoefficientPair C hC measure c hc x
  have hswap (ℓ₁ ℓ₂ : SmoothDual ρ) : B ℓ₂ ℓ₁ = conj (B ℓ₁ ℓ₂) :=
    LeftHaarDualForm.form_swap C hC measure c x ℓ₁ ℓ₂
  have hadd (ℓ₁ ℓ₂ ℓ₃ : SmoothDual ρ) : B (ℓ₁ + ℓ₂) ℓ₃ = B ℓ₁ ℓ₃ + B ℓ₂ ℓ₃ := by
    unfold B LeftHaarDualForm.form
    rw [LeftHaarDualForm.integrand_add_left]
    exact integral_add (hpair ℓ₁ ℓ₃) (hpair ℓ₂ ℓ₃)
  exact
    { inner := fun ℓ₁ ℓ₂ => B ℓ₂ ℓ₁
      conj_inner_symm := fun ℓ₁ ℓ₂ => (hswap ℓ₁ ℓ₂).symm
      re_inner_nonneg := fun ℓ => by
        change 0 ≤ (B ℓ ℓ).re
        dsimp only [B]
        rw [LeftHaarDualForm.form_self, Complex.ofReal_re]
        exact integral_nonneg fun q => (LeftHaarDualForm.integrand_self C hC c x ℓ q).2
      add_left := fun ℓ₁ ℓ₂ ℓ₃ => by
        change B ℓ₃ (ℓ₁ + ℓ₂) = B ℓ₃ ℓ₁ + B ℓ₃ ℓ₂
        rw [hswap (ℓ₁ + ℓ₂) ℓ₃, hadd, map_add, ← hswap, ← hswap]
      smul_left := fun ℓ₁ ℓ₂ a => by
        change B ℓ₂ (a • ℓ₁) = _
        unfold B
        rw [LeftHaarDualForm.form_swap C hC measure c x (a • ℓ₁) ℓ₂,
          LeftHaarDualForm.form_smul_left, map_mul, ← LeftHaarDualForm.form_swap]
      definite := fun ℓ hz => by
        by_contra hne
        have hℓ : ℓ.val ≠ 0 := fun he => hne (Subtype.ext he)
        obtain ⟨g, hg⟩ : ∃ g : H, ℓ.val (ρ g x) ≠ 0 := by
          by_contra hall
          simp only [not_exists, not_not] at hall
          apply hℓ
          have hle : Submodule.span ℂ (Set.range fun g : H => ρ g x) ≤ ℓ.val.ker := by
            rw [Submodule.span_le]
            rintro _ ⟨g, rfl⟩
            exact hall g
          exact LinearMap.ker_eq_top.mp (top_unique (hspan ▸ hle))
        have hp : 0 < (B ℓ ℓ).re := by
          dsimp only [B]
          rw [LeftHaarDualForm.form_self, Complex.ofReal_re,
            integral_pos_iff_support_of_nonneg
              (fun q => (LeftHaarDualForm.integrand_self C hC c x ℓ q).2) (hpair ℓ ℓ).re]
          have hcont : Continuous (fun q => (LeftHaarDualForm.integrand C hC c x ℓ ℓ q).re) :=
            Complex.continuous_re.comp (LeftHaarDualForm.continuous_integrand C hC c hρ x ℓ ℓ)
          refine hcont.isOpen_support.measure_pos measure ⟨QuotientGroup.mk g, ?_⟩
          rw [Function.mem_support, LeftHaarDualForm.integrand_self_mk, Complex.ofReal_re]
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
        change B ℓ ℓ = 0 at hz
        rw [hz, Complex.zero_re] at hp
        exact lt_irrefl _ hp
      invariant := fun g ℓ₁ ℓ₂ => by
        change B (smoothContragredient ρ g ℓ₂) (smoothContragredient ρ g ℓ₁) = B ℓ₂ ℓ₁
        unfold B LeftHaarDualForm.form
        rw [← integral_mul_left_of_continuous measure (QuotientGroup.mk g⁻¹)
          (LeftHaarDualForm.integrand C hC c x ℓ₂ ℓ₁)
          (LeftHaarDualForm.continuous_integrand C hC c hρ x ℓ₂ ℓ₁)
          (hpair ℓ₂ ℓ₁).aestronglyMeasurable]
        congr 1
        funext q
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
        change ℓ₂.val (ρ g⁻¹ (ρ k x)) * conj (ℓ₁.val (ρ g⁻¹ (ρ k x))) =
          ℓ₂.val (ρ (g⁻¹ * k) x) * conj (ℓ₁.val (ρ (g⁻¹ * k) x))
        simp only [map_mul, Module.End.mul_apply] }

end LeftHaarQuotientDualForm

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (C : Subgroup H) [C.Normal] (hC : C ≤ Subgroup.center H)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
  [MeasurableSpace (H ⧸ C)] (measure : Measure (H ⧸ C)) [measure.IsHaarMeasure]

/-- Square-integrable coefficient norms for the supplied quotient measure give unitarity. -/
theorem isUnitarizable_of_irreducible_quotient_memLp
    (hcof : ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ L ≤ K)
    (hsq : IsSquareIntegrableModCentralSubgroup C hC ρ measure) (hi : ρ.IsIrreducible) :
    IsUnitarizable ρ := by
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) ρ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨hadm, c, hc⟩ := hsq
  exact (isUnitarizable_smoothContragredient_of_admissible hcof
    (isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ hadm)
    ⟨LeftHaarQuotientDualForm.positiveForm C hC measure hadm.1 c hc x
      (span_range_orbit_eq_top hi hx)⟩).of_injective (smoothBidual hadm.1)
        (smoothBidual_injective_of_compact_cofinal hcof ρ hadm.1)

end Langlands.HarishChandraSchwartz
