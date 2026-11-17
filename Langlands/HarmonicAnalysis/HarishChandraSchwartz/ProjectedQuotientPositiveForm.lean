import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ProjectedDiscreteCoefficients

/-! # The actual quotient-L² form on projected left-level functions -/

noncomputable section

universe uG uV

open MeasureTheory
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

section SingleFunctional

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
  (A : Subgroup Γ) [A.Normal] {χ : A →* ℂˣ}
  (hχ : ∀ (a : A) (v : V), ρ a v = (χ a : ℂ) • v)
  (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1)
  [MeasurableSpace (Γ ⧸ A)] [BorelSpace (Γ ⧸ A)]
  (mu : Measure (Γ ⧸ A)) [mu.IsHaarMeasure]
  (hs : IsSmooth ρ) (ℓ : SmoothDual ρ)
  (hL2 : ∀ v : V, ∃ F : Γ ⧸ A → ℝ, MemLp F 2 mu ∧
    ∀ g : Γ, F (QuotientGroup.mk g) = ‖ℓ.val (ρ g v)‖)

include hs hL2

/-- A single functional with square-integrable coefficients suffices for
absolute convergence of its quotient coefficient products. -/
theorem integrable_formIntegrand_of_singleFunctional (v w : V) :
    Integrable (formIntegrand A hχ hu ℓ.val v w) mu := by
  obtain ⟨F, hF, hFg⟩ := hL2 v
  obtain ⟨G, hG, hGg⟩ := hL2 w
  apply (hF.integrable_mul hG).mono'
    (continuous_formIntegrand A hχ hu hs ℓ.val v w).aestronglyMeasurable
  filter_upwards [] with q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [formIntegrand_mk, norm_mul, Complex.norm_conj, Pi.mul_apply, hFg, hGg]

private theorem singleFunctional_invariantForm_add_left (v v' w : V) :
    invariantForm A mu hχ hu ℓ (v + v') w =
      invariantForm A mu hχ hu ℓ v w + invariantForm A mu hχ hu ℓ v' w := by
  unfold invariantForm
  rw [formIntegrand_add_left]
  exact integral_add
    (integrable_formIntegrand_of_singleFunctional A hχ hu mu hs ℓ hL2 v w)
    (integrable_formIntegrand_of_singleFunctional A hχ hu mu hs ℓ hL2 v' w)

/-- The quotient form is positive at every vector detected by a translate of
the specified functional. No irreducibility assumption is used. -/
theorem singleFunctional_invariantForm_re_pos {v : V} (g : Γ)
    (hg : ℓ.val (ρ g v) ≠ 0) : 0 < (invariantForm A mu hχ hu ℓ v v).re := by
  rw [invariantForm_self, Complex.ofReal_re]
  have hc : Continuous fun q => (formIntegrand A hχ hu ℓ.val v v q).re :=
    Complex.continuous_re.comp (continuous_formIntegrand A hχ hu hs ℓ.val v v)
  have hi := (integrable_formIntegrand_of_singleFunctional A hχ hu mu hs ℓ hL2 v v).re
  rw [integral_pos_iff_support_of_nonneg
    (fun q => (formIntegrand_self A hχ hu ℓ.val v q).2) hi]
  refine hc.isOpen_support.measure_pos mu ⟨QuotientGroup.mk g, ?_⟩
  rw [Function.mem_support, formIntegrand_self_mk, Complex.ofReal_re]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)

variable [mu.IsInvInvariant]

/-- Integrating one separating functional's coefficient products gives an
actual invariant positive form on the whole representation. -/
def singleFunctionalInvariantPositiveForm
    (hsep : ∀ v : V, (∀ g : Γ, ℓ.val (ρ g v) = 0) → v = 0) :
    InvariantPositiveForm ρ where
  inner v w := invariantForm A mu hχ hu ℓ w v
  conj_inner_symm v w := (invariantForm_swap A mu hχ hu ℓ v w).symm
  re_inner_nonneg v := by
    change 0 ≤ (invariantForm A mu hχ hu ℓ v v).re
    rw [invariantForm_self, Complex.ofReal_re]
    exact integral_nonneg fun q => (formIntegrand_self A hχ hu ℓ.val v q).2
  add_left v w x := by
    change invariantForm A mu hχ hu ℓ x (v + w) =
      invariantForm A mu hχ hu ℓ x v + invariantForm A mu hχ hu ℓ x w
    rw [invariantForm_swap A mu hχ hu ℓ (v + w) x,
      singleFunctional_invariantForm_add_left A hχ hu mu hs ℓ hL2,
      map_add, ← invariantForm_swap, ← invariantForm_swap]
  smul_left v w c := by
    change invariantForm A mu hχ hu ℓ w (c • v) = _
    rw [invariantForm_swap A mu hχ hu ℓ (c • v) w, invariantForm_smul_left,
      map_mul, ← invariantForm_swap]
  definite v hv := by
    by_contra hne
    obtain ⟨g, hg⟩ : ∃ g : Γ, ℓ.val (ρ g v) ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hne (hsep v hn)
    have hpos := singleFunctional_invariantForm_re_pos A hχ hu mu hs ℓ hL2 g hg
    change invariantForm A mu hχ hu ℓ v v = 0 at hv
    rw [hv, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  invariant g v w := invariantForm_rho A mu hχ hu ℓ g w v

end SingleFunctional

section ProjectedForm

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Nonempty (CompactOpenSubgroup Γ)]
  {Ξ σ : Γ → ℝ} {A : Subgroup Γ} [A.Normal]
  [MeasurableSpace A] [MeasurableMul A]
  (ht : TranslationWeights Ξ σ) (E : Submodule ℂ (Space Ξ σ))
  (hE : IsTranslationStable ht E) (hA : A ≤ Subgroup.center Γ)
  (muA : Measure A) [muA.IsMulRightInvariant]
  (χ : A →* ℂˣ) (hu : IsUnitaryCharacter χ)
  (hc : CentralIntegralConvergesOn E muA χ) (H : OpenSubgroup Γ)
  [MeasurableSpace (Γ ⧸ A)] [BorelSpace (Γ ⧸ A)]
  (mu : Measure (Γ ⧸ A)) [mu.IsHaarMeasure] [mu.IsInvInvariant]
  (hL2 : ∀ f :
      (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule,
    ∃ F : Γ ⧸ A → ℝ, MemLp F 2 mu ∧ ∀ g : Γ,
      F (QuotientGroup.mk g) = ‖(f : Γ → ℂ) g‖)

/-- The actual quotient-L² form on projected left-level Schwartz functions,
built from their square-integrable norms and smooth evaluation at one. -/
def projectedQuotientPositiveForm :
    InvariantPositiveForm
      (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation := by
  apply singleFunctionalInvariantPositiveForm A
    (projectedLeftSubrepresentation_central ht E hE hA muA χ hc H.toSubgroup)
    hu.norm_eq_one mu
    (isSmooth_projectedLeftSubrepresentation ht E hE hA muA χ hc H.toSubgroup)
    (projectedEvaluationAtOne ht E hE hA muA χ hc H)
  · intro f
    obtain ⟨F, hF, hFg⟩ := hL2 f
    refine ⟨F, hF, ?_⟩
    intro g
    change F (QuotientGroup.mk g) = ‖(f : Γ → ℂ) (1 * g)‖
    simpa only [one_mul] using hFg g
  · intro f hf
    apply Subtype.ext
    funext g
    change (f : Γ → ℂ) g = 0
    have hg := hf g
    change (f : Γ → ℂ) (1 * g) = 0 at hg
    simpa only [one_mul] using hg

/-- The constructed form is the literal quotient integral of the conjugate-first
product of the two actual functions, with the displayed quotient measure. -/
theorem projectedQuotientPositiveForm_inner
    (f g : (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule) :
    (projectedQuotientPositiveForm ht E hE hA muA χ hu hc H mu hL2).inner f g =
      ∫ q : Γ ⧸ A, conj ((f : Γ → ℂ) q.out) * (g : Γ → ℂ) q.out ∂mu := by
  change invariantForm A mu
    (projectedLeftSubrepresentation_central ht E hE hA muA χ hc H.toSubgroup)
    hu.norm_eq_one (projectedEvaluationAtOne ht E hE hA muA χ hc H) g f = _
  unfold invariantForm
  apply integral_congr_ae
  filter_upwards [] with q
  conv_lhs => rw [← Quotient.out_eq q]
  rw [formIntegrand_mk]
  change (g : Γ → ℂ) (1 * q.out) * conj ((f : Γ → ℂ) (1 * q.out)) = _
  simp only [one_mul, mul_comm]

end ProjectedForm

end Langlands.HarishChandraSchwartz
