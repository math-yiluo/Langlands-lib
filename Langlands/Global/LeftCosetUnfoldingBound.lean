import Langlands.Global.LeftCosetFundamentalDomain

/-! # Integrals over `Γ \ H` bounded by integrals over a covering set

For a discrete subgroup `Γ` of a second-countable topological group `H`, a left-invariant
measure `ν` and a measurable left `Γ`-invariant `f ≥ 0` on `H`, the integral over `Γ \ H` of
`y ↦ f(y.out)` for the discrete quotient measure is at most the integral of `f` over any set `Y`
whose left `Γ`-translates cover `H`.
-/

noncomputable section

universe u

open MeasureTheory Set
open scoped ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] (Γ : Subgroup H)

/-- The chosen representative of the coset of `g` is a left `Γ`-translate of `g`. -/
theorem exists_out_mk_eq_mul (g : H) : ∃ γ ∈ Γ, (mk Γ g).out = γ * g := by
  have h : mk Γ (mk Γ g).out = mk Γ g := Quotient.out_eq _
  rw [mk_eq_mk_iff] at h
  exact ⟨(g * (mk Γ g).out⁻¹)⁻¹, Γ.inv_mem h, by group⟩

/-- A left `Γ`-invariant function takes the same value at a point and at the chosen
representative of its coset. -/
theorem apply_out_mk {E : Type*} {f : H → E} (hinv : ∀ γ ∈ Γ, ∀ g : H, f (γ * g) = f g)
    (g : H) : f (mk Γ g).out = f g := by
  obtain ⟨γ, hγ, h⟩ := exists_out_mk_eq_mul Γ g
  rw [h, hinv γ hγ]

variable [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]

omit [TopologicalSpace H] [IsTopologicalGroup H] [BorelSpace H] in
/-- For a measurable left `Γ`-invariant `f`, the function `y ↦ f(y.out)` on `Γ \ H` is
measurable for the quotient σ-algebra. -/
theorem measurable_comp_out {f : H → ℝ≥0∞} (hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ g : H, f (γ * g) = f g) :
    Measurable (fun y : LeftCosetSpace Γ => f y.out) := by
  have hcomp : (fun y : LeftCosetSpace Γ => f y.out) ∘ mk Γ = f :=
    funext fun g => apply_out_mk Γ hinv g
  have hm : Measurable ((fun y : LeftCosetSpace Γ => f y.out) ∘ mk Γ) := by
    rw [hcomp]
    exact hf
  exact measurable_from_quotient.mpr hm

variable [SecondCountableTopology H]

/-- **Unfolding inequality.** Let `Γ` be discrete, `ν` a measure invariant under left
translation by `Γ`, `f ≥ 0` measurable and left `Γ`-invariant, and `Y ⊆ H` a set with
`Γ Y = H`. Then `∫_{Γ \ H} f(y.out) ≤ ∫_Y f` for the discrete quotient measure. -/
theorem lintegral_comp_out_le_setLIntegral (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H)
    [SMulInvariantMeasure Γ H ν] {f : H → ℝ≥0∞} (hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ g : H, f (γ * g) = f g) {Y : Set H}
    (hY : ∀ g : H, ∃ γ ∈ Γ, γ * g ∈ Y) :
    ∫⁻ y, f y.out ∂(discreteQuotientMeasure Γ hΓ ν) ≤ ∫⁻ x in Y, f x ∂ν := by
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  set D := fundamentalDomain Γ hΓ
  have hD : IsFundamentalDomain Γ D ν := isFundamentalDomain Γ hΓ ν
  rw [discreteQuotientMeasure, quotientMeasure,
    lintegral_map (measurable_comp_out Γ hf hinv) (measurable_mk Γ)]
  simp_rw [apply_out_mk Γ hinv]
  rw [hD.setLIntegral_eq_tsum' f Y]
  have h2 : ∀ (γ : Γ) (x : H), f (γ⁻¹ • x) = f x := fun γ x => hinv _ (γ⁻¹).2 x
  simp_rw [h2]
  have hcover : D ⊆ ⋃ γ : Γ, γ • Y ∩ D := by
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := hY x
    refine mem_iUnion.mpr ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    refine ⟨γ * x, hγx, ?_⟩
    change (γ⁻¹ : H) * (γ * x) = x
    group
  calc ∫⁻ x in D, f x ∂ν ≤ ∫⁻ x in ⋃ γ : Γ, γ • Y ∩ D, f x ∂ν := lintegral_mono_set hcover
    _ ≤ ∑' γ : Γ, ∫⁻ x in γ • Y ∩ D, f x ∂ν := lintegral_iUnion_le _ _

end Langlands.Global.LeftCosetSpace
