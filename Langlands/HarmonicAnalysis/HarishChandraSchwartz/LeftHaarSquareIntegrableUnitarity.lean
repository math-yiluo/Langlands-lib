import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity
import Langlands.Representation.OrbitSpan

/-! # Unitarity of irreducible square-integrable representations with left Haar measure

The positive form is placed on the smooth dual, so invariance uses left translation.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

namespace LeftHaarDualForm

/-- The product of two coefficients with a fixed vector descends to the central quotient. -/
def integrand (c : UnitaryCentralCharacter ρ) (x : V) (ℓ₁ ℓ₂ : SmoothDual ρ) :
    G ⧸ A → ℂ :=
  Quotient.lift (fun g => ℓ₁.val (ρ g x) * conj (ℓ₂.val (ρ g x))) (by
    intro g k hgk
    have hz : g⁻¹ * k ∈ A := QuotientGroup.leftRel_apply.mp hgk
    let z : Subgroup.center G := ⟨g⁻¹ * k, hA hz⟩
    have he (ℓ : SmoothDual ρ) :
        ℓ.val (ρ (g * (z : G)) x) = (c.character z : ℂ) * ℓ.val (ρ g x) :=
      c.matrixCoefficient_mul_center ℓ.val x g z
    have hχ : (c.character z : ℂ) * conj (c.character z : ℂ) = 1 := by
      rw [Complex.mul_conj', c.norm_eq_one]
      simp
    have e : ℓ₁.val (ρ (g * (z : G)) x) * conj (ℓ₂.val (ρ (g * (z : G)) x)) =
        ℓ₁.val (ρ g x) * conj (ℓ₂.val (ρ g x)) := by
      rw [he, he, map_mul, mul_mul_mul_comm, hχ, one_mul]
    simpa only [z, mul_inv_cancel_left] using e.symm)

omit [IsTopologicalGroup G] [A.Normal] in
@[simp]
theorem integrand_mk (c : UnitaryCentralCharacter ρ) (x : V) (ℓ₁ ℓ₂ : SmoothDual ρ)
    (g : G) :
    integrand A hA c x ℓ₁ ℓ₂ (QuotientGroup.mk g) =
      ℓ₁.val (ρ g x) * conj (ℓ₂.val (ρ g x)) := rfl

omit [IsTopologicalGroup G] [A.Normal] in
theorem integrand_swap (c : UnitaryCentralCharacter ρ) (x : V) (ℓ₁ ℓ₂ : SmoothDual ρ)
    (q : G ⧸ A) :
    integrand A hA c x ℓ₂ ℓ₁ q = conj (integrand A hA c x ℓ₁ ℓ₂ q) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [integrand_mk, map_mul, Complex.conj_conj, mul_comm]

omit [IsTopologicalGroup G] [A.Normal] in
theorem integrand_self_mk (c : UnitaryCentralCharacter ρ) (x : V) (ℓ : SmoothDual ρ)
    (g : G) :
    integrand A hA c x ℓ ℓ (QuotientGroup.mk g) =
      ((‖ℓ.val (ρ g x)‖ ^ 2 : ℝ) : ℂ) := by
  rw [integrand_mk, Complex.mul_conj', Complex.ofReal_pow]

omit [IsTopologicalGroup G] [A.Normal] in
theorem integrand_self (c : UnitaryCentralCharacter ρ) (x : V) (ℓ : SmoothDual ρ)
    (q : G ⧸ A) :
    integrand A hA c x ℓ ℓ q = ((integrand A hA c x ℓ ℓ q).re : ℂ) ∧
      0 ≤ (integrand A hA c x ℓ ℓ q).re := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [integrand_self_mk, Complex.ofReal_re]
  exact ⟨rfl, by positivity⟩

omit [IsTopologicalGroup G] [A.Normal] in
theorem integrand_add_left (c : UnitaryCentralCharacter ρ) (x : V)
    (ℓ₁ ℓ₂ ℓ₃ : SmoothDual ρ) :
    integrand A hA c x (ℓ₁ + ℓ₂) ℓ₃ =
      integrand A hA c x ℓ₁ ℓ₃ + integrand A hA c x ℓ₂ ℓ₃ := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change (ℓ₁.val (ρ g x) + ℓ₂.val (ρ g x)) * _ = _
  exact add_mul _ _ _

omit [IsTopologicalGroup G] [A.Normal] in
theorem integrand_smul_left (c : UnitaryCentralCharacter ρ) (x : V)
    (r : ℂ) (ℓ₁ ℓ₂ : SmoothDual ρ) :
    integrand A hA c x (r • ℓ₁) ℓ₂ =
      fun q => r * integrand A hA c x ℓ₁ ℓ₂ q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change (r * ℓ₁.val (ρ g x)) * _ = _
  exact mul_assoc _ _ _

omit [A.Normal] in
theorem continuous_integrand (c : UnitaryCentralCharacter ρ) (hρ : IsSmooth ρ)
    (x : V) (ℓ₁ ℓ₂ : SmoothDual ρ) :
    Continuous (integrand A hA c x ℓ₁ ℓ₂) := by
  have c₁ : Continuous fun g : G => ℓ₁.val (ρ g x) :=
    (matrixCoefficient_isLocallyConstant ρ ℓ₁.val x (hρ x)).continuous
  have c₂ : Continuous fun g : G => ℓ₂.val (ρ g x) :=
    (matrixCoefficient_isLocallyConstant ρ ℓ₂.val x (hρ x)).continuous
  exact (c₁.mul (Complex.continuous_conj.comp c₂)).quotient_lift _

variable [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure]

theorem integrable_integrand (c : UnitaryCentralCharacter ρ)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ)
    (x : V) (ℓ₁ ℓ₂ : SmoothDual ρ) :
    Integrable (integrand A hA c x ℓ₁ ℓ₂) μ := by
  obtain ⟨-, d, hd⟩ := id hρ
  have hi := (hd ℓ₁ x).integrable_mul (hd ℓ₂ x)
  refine hi.mono' ((continuous_integrand A hA c hρ.1.1 x ℓ₁ ℓ₂).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ‖integrand A hA c x ℓ₁ ℓ₂ (QuotientGroup.mk g)‖ ≤
    centralSubgroupCoefficientNorm A hA d ℓ₁.val x (QuotientGroup.mk g) *
      centralSubgroupCoefficientNorm A hA d ℓ₂.val x (QuotientGroup.mk g)
  rw [integrand_mk, norm_mul, Complex.norm_conj,
    centralSubgroupCoefficientNorm_mk, centralSubgroupCoefficientNorm_mk]
  exact le_rfl

/-- The form linear in the first functional; the positive form below swaps its arguments. -/
def form (c : UnitaryCentralCharacter ρ) (x : V) (ℓ₁ ℓ₂ : SmoothDual ρ) : ℂ :=
  ∫ q, integrand A hA c x ℓ₁ ℓ₂ q ∂μ

theorem form_add_left (c : UnitaryCentralCharacter ρ)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ)
    (x : V) (ℓ₁ ℓ₂ ℓ₃ : SmoothDual ρ) :
    form A hA μ c x (ℓ₁ + ℓ₂) ℓ₃ =
      form A hA μ c x ℓ₁ ℓ₃ + form A hA μ c x ℓ₂ ℓ₃ := by
  unfold form
  rw [integrand_add_left]
  exact integral_add (integrable_integrand A hA μ c hρ x ℓ₁ ℓ₃)
    (integrable_integrand A hA μ c hρ x ℓ₂ ℓ₃)

omit [IsTopologicalGroup G] [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure] in
theorem form_smul_left (c : UnitaryCentralCharacter ρ) (x : V)
    (r : ℂ) (ℓ₁ ℓ₂ : SmoothDual ρ) :
    form A hA μ c x (r • ℓ₁) ℓ₂ = r * form A hA μ c x ℓ₁ ℓ₂ := by
  unfold form
  rw [integrand_smul_left, integral_const_mul]

omit [IsTopologicalGroup G] [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure] in
theorem form_swap (c : UnitaryCentralCharacter ρ) (x : V) (ℓ₁ ℓ₂ : SmoothDual ρ) :
    form A hA μ c x ℓ₂ ℓ₁ = conj (form A hA μ c x ℓ₁ ℓ₂) := by
  unfold form
  simp_rw [integrand_swap A hA c x ℓ₁ ℓ₂]
  exact integral_conj

/-- The smooth-dual action translates the variable on the left. -/
theorem form_invariant (c : UnitaryCentralCharacter ρ) (x : V) (g : G)
    (ℓ₁ ℓ₂ : SmoothDual ρ) :
    form A hA μ c x (smoothContragredient ρ g ℓ₁) (smoothContragredient ρ g ℓ₂) =
      form A hA μ c x ℓ₁ ℓ₂ := by
  unfold form
  rw [← integral_mul_left_eq_self (integrand A hA c x ℓ₁ ℓ₂)
    (QuotientGroup.mk g⁻¹ : G ⧸ A)]
  congr 1
  funext q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  change ℓ₁.val (ρ g⁻¹ (ρ k x)) * conj (ℓ₂.val (ρ g⁻¹ (ρ k x))) =
    ℓ₁.val (ρ (g⁻¹ * k) x) * conj (ℓ₂.val (ρ (g⁻¹ * k) x))
  simp only [map_mul, Module.End.mul_apply]

omit [IsTopologicalGroup G] [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure] in
theorem form_self (c : UnitaryCentralCharacter ρ) (x : V) (ℓ : SmoothDual ρ) :
    form A hA μ c x ℓ ℓ = ((∫ q, (integrand A hA c x ℓ ℓ q).re ∂μ : ℝ) : ℂ) := by
  unfold form
  rw [← integral_complex_ofReal]
  congr 1
  funext q
  exact (integrand_self A hA c x ℓ q).1

theorem form_self_re_pos (c : UnitaryCentralCharacter ρ)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (x : V)
    (ℓ : SmoothDual ρ) (g : G) (hg : ℓ.val (ρ g x) ≠ 0) :
    0 < (form A hA μ c x ℓ ℓ).re := by
  rw [form_self, Complex.ofReal_re]
  have hc : Continuous fun q => (integrand A hA c x ℓ ℓ q).re :=
    Complex.continuous_re.comp (continuous_integrand A hA c hρ.1.1 x ℓ ℓ)
  have hi := (integrable_integrand A hA μ c hρ x ℓ ℓ).re
  rw [integral_pos_iff_support_of_nonneg (fun q => (integrand_self A hA c x ℓ q).2) hi]
  refine hc.isOpen_support.measure_pos μ ⟨QuotientGroup.mk g, ?_⟩
  rw [Function.mem_support, integrand_self_mk, Complex.ofReal_re]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)

/-- A spanning orbit makes the integrated form definite on the smooth dual. -/
def positiveForm (c : UnitaryCentralCharacter ρ)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (x : V)
    (hspan : Submodule.span ℂ (Set.range fun g : G => ρ g x) = ⊤) :
    InvariantPositiveForm (smoothContragredient ρ) where
  inner ℓ₁ ℓ₂ := form A hA μ c x ℓ₂ ℓ₁
  conj_inner_symm ℓ₁ ℓ₂ := (form_swap A hA μ c x ℓ₁ ℓ₂).symm
  re_inner_nonneg ℓ := by
    show 0 ≤ (form A hA μ c x ℓ ℓ).re
    rw [form_self, Complex.ofReal_re]
    exact integral_nonneg fun q => (integrand_self A hA c x ℓ q).2
  add_left ℓ₁ ℓ₂ ℓ₃ := by
    change form A hA μ c x ℓ₃ (ℓ₁ + ℓ₂) = _
    rw [form_swap A hA μ c x (ℓ₁ + ℓ₂) ℓ₃,
      form_add_left A hA μ c hρ x ℓ₁ ℓ₂ ℓ₃, map_add, ← form_swap, ← form_swap]
  smul_left ℓ₁ ℓ₂ r := by
    change form A hA μ c x ℓ₂ (r • ℓ₁) = _
    rw [form_swap A hA μ c x (r • ℓ₁) ℓ₂, form_smul_left, map_mul, ← form_swap]
  definite ℓ hzero := by
    by_contra hne
    have hℓ : ℓ.val ≠ 0 := fun he => hne (Subtype.ext he)
    obtain ⟨g, hg⟩ : ∃ g : G, ℓ.val (ρ g x) ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      apply hℓ
      have hle : Submodule.span ℂ (Set.range fun g : G => ρ g x) ≤ ℓ.val.ker := by
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        exact hall g
      have hker : ℓ.val.ker = ⊤ := top_unique (hspan ▸ hle)
      exact LinearMap.ker_eq_top.mp hker
    have hpos := form_self_re_pos A hA μ c hρ x ℓ g hg
    rw [hzero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  invariant g ℓ₁ ℓ₂ := form_invariant A hA μ c x g ℓ₂ ℓ₁

end LeftHaarDualForm

variable [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure]

/-- Irreducible square-integrable representations are unitarizable using only left Haar
measure on the central quotient and a cofinal supply of compact open subgroups. -/
theorem isUnitarizable_of_irreducible_isSquareIntegrable_leftHaar
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (hi : ρ.IsIrreducible) :
    IsUnitarizable ρ := by
  have : Nontrivial V := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨-, c, -⟩ := id hρ
  have hdual : IsUnitarizable (smoothContragredient ρ) :=
    ⟨LeftHaarDualForm.positiveForm A hA μ c hρ x (span_range_orbit_eq_top hi hx)⟩
  exact (isUnitarizable_smoothContragredient_of_admissible hcof
    (isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ hρ.1) hdual).of_injective
    (smoothBidual hρ.1.1) (smoothBidual_injective_of_compact_cofinal hcof ρ hρ.1.1)

end Langlands.HarishChandraSchwartz
