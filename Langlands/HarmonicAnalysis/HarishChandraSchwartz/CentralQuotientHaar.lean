import Langlands.Analysis.Local.NormalSubgroupHaarModulus

/-! # Compatible measures on `A \ G` and Haar measures on `G ⧸ A` for central `A`

Waldspurger states square integrability modulo `A_G` on `A_G \ G` with the quotient of the Haar
measures of `G` and `A_G` (Lemma III.1.3, proof of Theorem VIII.4.2), and the integrals of
`HarishChandraSchwartz` are written for a compatible measure `ν` on `A \ G` (`IsCompatible`).
`DiscreteCoefficientSpace` states square integrability on the quotient group `G ⧸ A` with an
arbitrary Haar measure `μ`. This module compares the two for a closed central subgroup `A` and
a left invariant measure `μ_G` on `G`:

* `quotientLeftTranslate`: the left translation `A g ↦ A h g` of `A \ G`;
* `IsCompatible.map_quotientLeftTranslate`: `ν` is invariant under it;
* `IsCompatible.exists_smul_eq_map`: the image of `ν` on `G ⧸ A` is `c • μ` with `c ≠ 0`;
* `IsCompatible.memLp_of_memLp_comp`, `IsCompatible.exists_memLp_quotientGroup`: `L^p`
  membership for `ν` on `A \ G` gives `L^p` membership for `μ` on `G ⧸ A`.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal CompactlySupported

namespace Langlands.QuotientIntegration

universe u

section Packaging

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The left translation `A g ↦ A h g` of `A \ G`, for a normal subgroup `A`. -/
def quotientLeftTranslate (A : Subgroup G) [A.Normal] (h : G) :
    LeftQuotient A ≃ₜ LeftQuotient A :=
  Homeomorph.Quotient.congr (Homeomorph.mulLeft h) (by
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ A ↔ (h * y) * (h * x)⁻¹ ∈ A
    rw [show (h * y) * (h * x)⁻¹ = h * (y * x⁻¹ * h⁻¹) by group,
      Subgroup.Normal.mem_comm_iff (inferInstance : A.Normal) (a := h) (b := y * x⁻¹ * h⁻¹),
      show y * x⁻¹ * h⁻¹ * h = y * x⁻¹ by group])

@[simp] theorem quotientLeftTranslate_mk (A : Subgroup G) [A.Normal] (h g : G) :
    quotientLeftTranslate A h (Quotient.mk _ g) = Quotient.mk _ (h * g) := rfl

end Packaging

section Measure

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} (hA : IsClosed (A : Set G)) [A.Normal] (hAc : A ≤ Subgroup.center G)
  [MeasurableSpace A] [BorelSpace A]
  {μG : Measure G} [μG.IsMulLeftInvariant]
  {μA : Measure A} [IsHaarMeasure μA] [μA.Regular] [IsMulRightInvariant μA]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {ν : Measure (LeftQuotient A)}

omit [BorelSpace (LeftQuotient A)] in
include hA hAc in
/-- For central `A` and left invariant `μ_G`, compact real tests on `A \ G` have the same
`ν`-integral after the left translation `A g ↦ A h g`. -/
theorem IsCompatible.integral_comp_quotientLeftTranslate (hν : IsCompatible A μG μA ν)
    (h : G) (φ : C_c(LeftQuotient A, ℝ)) :
    ∫ q, φ (quotientLeftTranslate A h q) ∂ν = ∫ q, φ q ∂ν := by
  obtain ⟨f, hf, -⟩ := realQuotientPositiveLifting A hA μA φ
  have hφ : ∀ q, φ q = quotientAverageReal A μA f q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g => exact (hf g).symm
  have hφh : ∀ q, φ (quotientLeftTranslate A h q) =
      quotientAverageReal A μA (fun x => f (h * x)) q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [quotientLeftTranslate_mk, ← hf (h * g), quotientAverageReal_mk]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      have hc : (a : G) * h = h * a := (Subgroup.mem_center_iff.mp (hAc a.2) h).symm
      simp only [← mul_assoc, hc]
  simp_rw [hφh, hφ]
  rw [hν.integral_quotientAverageReal (fun x => f (h * x))
      (f.continuous.comp (Homeomorph.mulLeft h).continuous)
      (f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft h)),
    hν.integral_quotientAverageReal f f.continuous f.hasCompactSupport]
  exact integral_mul_left_eq_self (fun x => f x) h

include hA hAc in
/-- **A compatible measure on `A \ G` is invariant under left translations** when `A` is
central and `μ_G` is left invariant. -/
theorem IsCompatible.map_quotientLeftTranslate (hν : IsCompatible A μG μA ν) (h : G) :
    Measure.map (quotientLeftTranslate A h) ν = ν := by
  have := leftQuotient_t2Space A hA
  have := leftQuotient_locallyCompactSpace (G := G) A
  have : ν.Regular := hν.regular
  have : (Measure.map (quotientLeftTranslate A h) ν).Regular :=
    Measure.Regular.map (quotientLeftTranslate A h)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  have hmap : (∫ q, φ q ∂Measure.map (quotientLeftTranslate A h) ν) =
      ∫ q, φ (quotientLeftTranslate A h q) ∂ν :=
    integral_map_equiv (quotientLeftTranslate A h).toMeasurableEquiv φ
  rw [hmap]
  exact hν.integral_comp_quotientLeftTranslate hA hAc h φ

variable [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]

include hA hAc in
/-- The image of `ν` on the quotient group `G ⧸ A` is left invariant. -/
theorem IsCompatible.isMulLeftInvariant_map_normalLeftQuotientHomeomorph
    (hν : IsCompatible A μG μA ν) :
    (Measure.map (normalLeftQuotientHomeomorph A) ν).IsMulLeftInvariant := by
  have he : Measurable (normalLeftQuotientHomeomorph A) :=
    (normalLeftQuotientHomeomorph A).continuous.measurable
  refine ⟨fun x => ?_⟩
  induction x using QuotientGroup.induction_on with
  | H h =>
    have hc : (fun y : G ⧸ A => (h : G ⧸ A) * y) ∘ normalLeftQuotientHomeomorph A =
        normalLeftQuotientHomeomorph A ∘ quotientLeftTranslate A h := by
      funext q
      induction q using Quotient.inductionOn with
      | h x => rfl
    rw [Measure.map_map (measurable_const_mul _) he, hc,
      ← Measure.map_map he (quotientLeftTranslate A h).continuous.measurable,
      hν.map_quotientLeftTranslate hA hAc h]

include hA hAc in
/-- **Comparison with a Haar measure on `G ⧸ A`**: the image of `ν` is a nonzero multiple of
every Haar measure `μ` on `G ⧸ A`. -/
theorem IsCompatible.exists_smul_eq_map [SecondCountableTopology G]
    (hν : IsCompatible A μG μA ν) (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map (normalLeftQuotientHomeomorph A) ν = c • μ := by
  have he : Measurable (normalLeftQuotientHomeomorph A) :=
    (normalLeftQuotientHomeomorph A).continuous.measurable
  have := hν.isMulLeftInvariant_map_normalLeftQuotientHomeomorph hA hAc
  have : ν.Regular := hν.regular
  have : (Measure.map (normalLeftQuotientHomeomorph A) ν).Regular :=
    Measure.Regular.map (normalLeftQuotientHomeomorph A)
  have hmap := isMulLeftInvariant_eq_smul (Measure.map (normalLeftQuotientHomeomorph A) ν) μ
  refine ⟨_, fun h0 => hν.nonzero ?_, hmap⟩
  rw [h0, zero_smul] at hmap
  exact (Measure.map_eq_zero_iff he.aemeasurable).mp hmap

include hA hAc in
/-- **`L^p` transfer**: if `q ↦ F(A q)` is in `L^p(A \ G, ν)`, then `F ∈ L^p(G ⧸ A, μ)` for
every Haar measure `μ`. -/
theorem IsCompatible.memLp_of_memLp_comp [SecondCountableTopology G]
    (hν : IsCompatible A μG μA ν) (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] {E : Type*}
    [NormedAddCommGroup E] {F : G ⧸ A → E} {p : ℝ≥0∞}
    (hF : MemLp (fun q => F (normalLeftQuotientHomeomorph A q)) p ν) : MemLp F p μ := by
  obtain ⟨c, hc, hmap⟩ := hν.exists_smul_eq_map hA hAc μ
  have h1 : MemLp F p (Measure.map (normalLeftQuotientHomeomorph A) ν) :=
    ((normalLeftQuotientHomeomorph A).toMeasurableEquiv.memLp_map_measure_iff).2 hF
  have hμ : μ = c⁻¹ • Measure.map (normalLeftQuotientHomeomorph A) ν := by
    rw [hmap, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hμ]
  exact h1.smul_measure ENNReal.coe_ne_top

include hA hAc in
/-- A function in `L^p(A \ G, ν)` descends to a function in `L^p(G ⧸ A, μ)` with the same
values on cosets. -/
theorem IsCompatible.exists_memLp_quotientGroup [SecondCountableTopology G]
    (hν : IsCompatible A μG μA ν) (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] {E : Type*}
    [NormedAddCommGroup E] {F₀ : LeftQuotient A → E} {p : ℝ≥0∞} (hF₀ : MemLp F₀ p ν) :
    ∃ F : G ⧸ A → E, MemLp F p μ ∧ ∀ g : G, F (g : G ⧸ A) = F₀ (Quotient.mk _ g) := by
  refine ⟨fun x => F₀ ((normalLeftQuotientHomeomorph A).symm x), ?_, fun g => ?_⟩
  · refine hν.memLp_of_memLp_comp hA hAc μ ?_
    simpa only [Homeomorph.symm_apply_apply] using hF₀
  · change F₀ ((normalLeftQuotientHomeomorph A).symm (g : G ⧸ A)) = _
    rw [(normalLeftQuotientHomeomorph A).symm_apply_eq.mpr
      (normalLeftQuotientHomeomorph_mk A g).symm]

end Measure

end Langlands.QuotientIntegration
