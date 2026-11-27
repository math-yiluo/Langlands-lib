import Langlands.Global.LeftCosetUnfoldingBound

/-! # Conjugation counts on a discrete left quotient

Let `Γ` be a discrete subgroup of a second-countable topological group `H` with a left-invariant
measure `ν`, and let `μΓ` be the discrete quotient measure on `Γ \ H`. For `C ⊆ H` and `t ∈ H`,
`conjugationCount Γ C t` is the number of `q ∈ Γ` with `t⁻¹ q t ∈ C`, and
`translateCount Γ A t` is the number of `γ ∈ Γ` with `γ t ∈ A`.

All integrals are lower Lebesgue integrals `∫⁻` of `ℝ≥0∞`-valued functions.

* `translateCount` unfolds: `∫⁻_{Γ \ H} translateCount Γ A (y.out) dμΓ(y) = ν(A)` for measurable
  `A` (`lintegral_translateCount_out`).
* If `t = γ₀ x d` with `γ₀ ∈ Γ` and `d ∈ D`, then the conjugation count of `C` at `t` is at
  most the translate count at `t` of `x (D C)` (`conjugationCount_le_translateCount`).
* Consequently (`lintegral_conjugationCount_mul_le`): let `y : ι → H` be a family indexed by a
  countable type, let `C, D ⊆ H` with `D C` measurable, and let `w : Γ \ H → ℝ≥0∞` and
  `Φ : ι → ℝ≥0∞`. Suppose every coset `z` has witnesses `i`, `γ ∈ Γ` and `d ∈ D` with
  `z.out = γ y_i d` and `w z ≤ Φ i`. Then
  `∫⁻_{Γ \ H} conjugationCount Γ C (z.out) · w z dμΓ(z) ≤ (∑ᵢ Φ i) · ν(D C)`.

The comparison of the count with the periodization of an indicator function is the unfolding
argument behind the counting form of the standard measure of Bernstein, *On the support of
Plancherel measure* (1988), §3.3, whose density is the reciprocal volume of the image of a
translate of a ball. -/

noncomputable section

universe u v

open MeasureTheory Set
open scoped ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] (Γ : Subgroup H)

/-- The number `#{q ∈ Γ : t⁻¹ q t ∈ C}` of elements of `Γ` conjugated into `C` by `t`, in
`ℝ≥0∞`. -/
def conjugationCount (C : Set H) (t : H) : ℝ≥0∞ :=
  (({q : H | q ∈ Γ ∧ t⁻¹ * q * t ∈ C}.encard : ℕ∞) : ℝ≥0∞)

/-- The number `#{γ ∈ Γ : γ t ∈ A}` of left `Γ`-translates of `t` in `A`, in `ℝ≥0∞`. -/
def translateCount (A : Set H) (t : H) : ℝ≥0∞ :=
  ∑' γ : Γ, A.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : H) * t)

/-- The translate count is left `Γ`-invariant. -/
theorem translateCount_mul (A : Set H) {γ₀ : H} (hγ₀ : γ₀ ∈ Γ) (t : H) :
    translateCount Γ A (γ₀ * t) = translateCount Γ A t := by
  unfold translateCount
  rw [← (Equiv.mulRight (⟨γ₀, hγ₀⟩ : Γ)).tsum_eq
    (fun γ : Γ => A.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : H) * t))]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc]

/-- **Count comparison.** If `t = γ₀ x d` with `γ₀ ∈ Γ` and `d ∈ D`, every `q ∈ Γ` with
`t⁻¹ q t ∈ C` gives the element `γ₀⁻¹ q ∈ Γ`, which carries `t` into `x (D C)`. -/
theorem conjugationCount_le_translateCount (C D : Set H) {x t γ₀ d : H} (hγ₀ : γ₀ ∈ Γ)
    (hd : d ∈ D) (ht : t = γ₀ * x * d) :
    conjugationCount Γ C t ≤ translateCount Γ ((fun u => x⁻¹ * u) ⁻¹' (D * C)) t := by
  set S : Set H := {q : H | q ∈ Γ ∧ t⁻¹ * q * t ∈ C}
  let g : S → Γ := fun q => ⟨γ₀⁻¹ * q, Γ.mul_mem (Γ.inv_mem hγ₀) q.2.1⟩
  have hg : Function.Injective g := by
    intro q₁ q₂ h
    have h' : γ₀⁻¹ * (q₁ : H) = γ₀⁻¹ * q₂ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel h')
  have hone : ∀ q : S, ((fun u => x⁻¹ * u) ⁻¹' (D * C)).indicator (fun _ => (1 : ℝ≥0∞))
      ((g q : H) * t) = 1 := by
    intro q
    refine Set.indicator_of_mem ?_ _
    obtain ⟨-, hc⟩ := q.2
    refine ⟨d, hd, t⁻¹ * q * t, hc, ?_⟩
    change d * (t⁻¹ * q * t) = x⁻¹ * (γ₀⁻¹ * q * t)
    rw [ht]
    group
  unfold conjugationCount translateCount
  rw [← ENNReal.tsum_set_one]
  calc ∑' _ : S, (1 : ℝ≥0∞)
      = ∑' q : S, ((fun u => x⁻¹ * u) ⁻¹' (D * C)).indicator (fun _ => (1 : ℝ≥0∞))
          ((g q : H) * t) := tsum_congr fun q => (hone q).symm
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hg
        (fun γ : Γ => ((fun u => x⁻¹ * u) ⁻¹' (D * C)).indicator (fun _ => (1 : ℝ≥0∞))
          ((γ : H) * t))

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

omit [SecondCountableTopology H] in
/-- The translate count of a measurable set is measurable. -/
theorem measurable_translateCount [Countable Γ] {A : Set H} (hA : MeasurableSet A) :
    Measurable (translateCount Γ A) :=
  Measurable.tsum fun γ =>
    (measurable_const.indicator hA).comp (measurable_const_mul (γ : H))

variable (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H) [ν.IsMulLeftInvariant]

/-- **Unfolding of the translate count.** For measurable `A`,
`∫⁻_{Γ \ H} #{γ ∈ Γ : γ y.out ∈ A} dμΓ(y) = ν(A)`. -/
theorem lintegral_translateCount_out {A : Set H} (hA : MeasurableSet A) :
    ∫⁻ y, translateCount Γ A y.out ∂(discreteQuotientMeasure Γ hΓ ν) = ν A := by
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  set s := fundamentalDomain Γ hΓ
  have hinv : ∀ γ ∈ Γ, ∀ g : H, translateCount Γ A (γ * g) = translateCount Γ A g :=
    fun γ hγ g => translateCount_mul Γ A hγ g
  have hm := measurable_translateCount Γ hA
  set k : H → ℝ≥0∞ := A.indicator (fun _ => (1 : ℝ≥0∞))
  have hk : Measurable k := measurable_const.indicator hA
  rw [discreteQuotientMeasure, quotientMeasure,
    lintegral_map (measurable_comp_out Γ hm hinv) (measurable_mk Γ)]
  simp_rw [apply_out_mk Γ hinv]
  calc ∫⁻ x in s, translateCount Γ A x ∂ν
      = ∫⁻ x in s, ∑' γ : Γ, k ((γ : H) * x) ∂ν := rfl
    _ = ∑' γ : Γ, ∫⁻ x in s, k ((γ : H) * x) ∂ν := by
        rw [lintegral_tsum]
        intro γ
        exact (hk.comp (measurable_const_mul _)).aemeasurable
    _ = ∫⁻ x, k x ∂ν := ((isFundamentalDomain Γ hΓ ν).lintegral_eq_tsum'' k).symm
    _ = ν A := lintegral_indicator_one hA

/-- **Integrated conjugation counts.** Let `y : ι → H` be a countable family, `D, C ⊆ H` with
`D C` measurable, `w : Γ \ H → ℝ≥0∞` any function and `Φ : ι → ℝ≥0∞`. Suppose every coset `z`
has witnesses `i`, `γ ∈ Γ` and `d ∈ D` with `z.out = γ y_i d` and `w z ≤ Φ i`. Then the lower
integral satisfies `∫⁻ conjugationCount Γ C (z.out) · w z dμΓ ≤ (∑ᵢ Φ i) · ν(D C)`. -/
theorem lintegral_conjugationCount_mul_le {ι : Type v} [Countable ι] (y : ι → H)
    (C D : Set H) (hDC : MeasurableSet (D * C)) (w : LeftCosetSpace Γ → ℝ≥0∞) (Φ : ι → ℝ≥0∞)
    (hcover : ∀ z : LeftCosetSpace Γ, ∃ i, ∃ γ ∈ Γ, ∃ d ∈ D,
      z.out = γ * y i * d ∧ w z ≤ Φ i) :
    ∫⁻ z, conjugationCount Γ C z.out * w z ∂(discreteQuotientMeasure Γ hΓ ν) ≤
      (∑' i, Φ i) * ν (D * C) := by
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  set A : ι → Set H := fun i => (fun u => (y i)⁻¹ * u) ⁻¹' (D * C)
  have hA : ∀ i, MeasurableSet (A i) := fun i => (measurable_const_mul _) hDC
  have hinv : ∀ i, ∀ γ ∈ Γ, ∀ g : H, translateCount Γ (A i) (γ * g) = translateCount Γ (A i) g :=
    fun i γ hγ g => translateCount_mul Γ (A i) hγ g
  have hpoint : ∀ z : LeftCosetSpace Γ, conjugationCount Γ C z.out * w z ≤
      ∑' i, Φ i * translateCount Γ (A i) z.out := by
    intro z
    obtain ⟨i, γ, hγ, d, hd, hz, hw⟩ := hcover z
    calc conjugationCount Γ C z.out * w z
        ≤ translateCount Γ (A i) z.out * Φ i :=
          mul_le_mul' (conjugationCount_le_translateCount Γ C D hγ hd hz) hw
      _ = Φ i * translateCount Γ (A i) z.out := mul_comm _ _
      _ ≤ ∑' i, Φ i * translateCount Γ (A i) z.out :=
          ENNReal.le_tsum (f := fun i => Φ i * translateCount Γ (A i) z.out) i
  calc ∫⁻ z, conjugationCount Γ C z.out * w z ∂(discreteQuotientMeasure Γ hΓ ν)
      ≤ ∫⁻ z, ∑' i, Φ i * translateCount Γ (A i) z.out ∂(discreteQuotientMeasure Γ hΓ ν) :=
        lintegral_mono hpoint
    _ = ∑' i, ∫⁻ z, Φ i * translateCount Γ (A i) z.out ∂(discreteQuotientMeasure Γ hΓ ν) := by
        rw [lintegral_tsum]
        intro i
        exact ((measurable_comp_out Γ (measurable_translateCount Γ (hA i)) (hinv i)).const_mul
          _).aemeasurable
    _ = ∑' i, Φ i * ν (D * C) := by
        refine tsum_congr fun i => ?_
        rw [lintegral_const_mul _ (measurable_comp_out Γ (measurable_translateCount Γ (hA i))
          (hinv i)), lintegral_translateCount_out Γ hΓ ν (hA i), measure_preimage_mul]
    _ = (∑' i, Φ i) * ν (D * C) := ENNReal.tsum_mul_right

end Langlands.Global.LeftCosetSpace
