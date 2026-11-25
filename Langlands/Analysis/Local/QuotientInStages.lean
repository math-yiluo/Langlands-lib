import Langlands.Analysis.Local.QuotientNormalizingFunction

/-!
# Quotients in stages for a discrete subgroup of a closed subgroup

Let `H` be a closed subgroup of `G` with a right-invariant measure `μH`, `Λ ≤ H` a discrete subgroup,
and `νΛ`, `νH`, `νΛH` compatible measures on `Λ \ G`, `H \ G` and `(Λ ∩ H) \ H` (counting measure on
`Λ`). If `νΛH` has finite total mass, then for a measurable left `H`-invariant `F` the function
descended to `Λ \ G` is integrable exactly when the one descended to `H \ G` is, and

`∫_{Λ \ G} F dνΛ = νΛH((Λ ∩ H) \ H) · ∫_{H \ G} F dνH`.

The proof divides a normalizing function of `Λ` by the total mass of `νΛH` and obtains a normalizing
function of `H` (`IsCompatible.isNormalizingFunction_div_measure_univ`); both integrals are then
integrals over `G` by the rule of `QuotientNormalizingFunction`.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal

universe u

/-- A left `H`-invariant function is left `Λ`-invariant for `Λ ≤ H`. -/
theorem descend_invariant_of_le {G : Type u} [Group G] {H Λ : Subgroup G} (hΛH : Λ ≤ H)
    {A : Sort*} {F : G → A} (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    ∀ l : Λ, ∀ g, F (l.val * g) = F g :=
  fun l g => hF ⟨l.val, hΛH l.2⟩ g

/-- The two weighted integrands differ by the factor `c.toReal⁻¹`. -/
private theorem toReal_div_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a c : ℝ≥0∞) (v : E) : (a / c).toReal • v = (c.toReal)⁻¹ • (a.toReal • v) := by
  rw [ENNReal.toReal_div, smul_smul, div_eq_mul_inv, mul_comm]

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [MeasurableSpace H] [BorelSpace H]
  {μH : Measure H} [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
  {Λ : Subgroup G} [DiscreteTopology Λ] {Λ' : Subgroup H}
  [MeasurableSpace (LeftQuotient Λ')] [BorelSpace (LeftQuotient Λ')]
  {νΛ' : Measure (LeftQuotient Λ')}

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [BorelSpace H] [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
  [DiscreteTopology Λ] [MeasurableSpace (LeftQuotient Λ')] [BorelSpace (LeftQuotient Λ')] in
/-- The subgroup `Λ'` of `H` with `x ∈ Λ' ↔ x ∈ Λ` is in bijection with `Λ` when `Λ ≤ H`. -/
private def subgroupOfEquiv (hΛH : Λ ≤ H) (hΛ' : ∀ x : H, x ∈ Λ' ↔ (x : G) ∈ Λ) : Λ' ≃ Λ where
  toFun l := ⟨l.val.val, (hΛ' l.val).1 l.2⟩
  invFun l := ⟨⟨l.val, hΛH l.2⟩, (hΛ' _).2 l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
  [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [MeasurableSpace (LeftQuotient Λ')]
  [BorelSpace (LeftQuotient Λ')] in
private theorem isDiscrete_of_iff (hΛ' : ∀ x : H, x ∈ Λ' ↔ (x : G) ∈ Λ) :
    IsDiscrete (Λ' : Set H) := by
  have h : (Λ' : Set H) = Subtype.val ⁻¹' (Λ : Set G) := by
    ext x
    exact hΛ' x
  rw [h]
  exact (SetLike.isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology Λ›).preimage
    continuous_subtype_val.continuousOn Subtype.val_injective

omit [μH.IsMulRightInvariant] in
/-- **A normalizing function of `Λ` divided by the mass of `νΛ'` is one of `H`.** If `ρ` is a
normalizing function of the discrete subgroup `Λ ≤ H` for the counting measure, and `νΛ'` on
`Λ' \ H` (`Λ' = Λ ∩ H` as a subgroup of `H`) is compatible with `(μH, Measure.count)` and has
finite total mass, then `∫⁻ h, ρ (h g) ∂μH = νΛ' univ` for every `g`, and `ρ / νΛ' univ` is a
normalizing function of `H`. -/
theorem IsCompatible.isNormalizingFunction_div_measure_univ (hH : IsClosed (H : Set G))
    (hΛH : Λ ≤ H) (hΛ' : ∀ x : H, x ∈ Λ' ↔ (x : G) ∈ Λ)
    (hνΛ' : IsCompatible Λ' μH Measure.count νΛ') (hfin : νΛ' Set.univ ≠ ⊤)
    {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction Λ Measure.count ρ) :
    IsNormalizingFunction H μH (fun g => ρ g / νΛ' Set.univ) := by
  have := hH.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have hd := isDiscrete_of_iff hΛ'
  have : DiscreteTopology Λ' := SetLike.isDiscrete_iff_discreteTopology.mp hd
  have hΛ'c : IsClosed (Λ' : Set H) := Λ'.isClosed_of_isDiscrete hd
  have : IsFiniteMeasureOnCompacts (Measure.count : Measure Λ') :=
    ⟨fun _ hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete⟩
  have hsum := ((isNormalizingFunction_count_iff Λ ρ).1 hρ).2
  have hmass : ∀ g : G, ∫⁻ h : H, ρ (h.val * g) ∂μH = νΛ' Set.univ := by
    intro g
    have hm : Measurable fun h : H => ρ (h.val * g) :=
      hρ.measurable.comp (continuous_subtype_val.mul_const g).measurable
    rw [hνΛ'.lintegral_eq_lintegral_quotientAverageENNReal hΛ'c _ hm]
    rw [← lintegral_one]
    refine lintegral_congr fun q => ?_
    induction q using Quotient.inductionOn with
    | h x =>
      rw [quotientAverageENNReal_mk, lintegral_count, ← hsum (x.val * g),
        ← (subgroupOfEquiv hΛH hΛ').tsum_eq (fun l : Λ => ρ (l.val * (x.val * g)))]
      refine tsum_congr fun l => ?_
      simp [subgroupOfEquiv, mul_assoc]
  have h0 : νΛ' Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hνΛ'.nonzero
  refine ⟨hρ.measurable.div_const _, fun g => ?_⟩
  simp_rw [div_eq_mul_inv]
  have hm : Measurable fun h : H => ρ (h.val * g) :=
    hρ.measurable.comp (continuous_subtype_val.mul_const g).measurable
  rw [lintegral_mul_const _ hm, hmass g, ENNReal.mul_inv_cancel h0 hfin]

variable [MeasurableSpace (LeftQuotient Λ)] [BorelSpace (LeftQuotient Λ)]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG]
  {νΛ : Measure (LeftQuotient Λ)} {νH : Measure (LeftQuotient H)}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- **Quotients in stages, integrability.** -/
theorem IsCompatible.integrable_descend_iff_of_le (hH : IsClosed (H : Set G)) (hΛH : Λ ≤ H)
    (hΛ' : ∀ x : H, x ∈ Λ' ↔ (x : G) ∈ Λ)
    (hνΛ : IsCompatible Λ μG Measure.count νΛ) (hνH : IsCompatible H μG μH νH)
    (hνΛ' : IsCompatible Λ' μH Measure.count νΛ') (hfin : νΛ' Set.univ ≠ ⊤)
    (F : G → E) (hFm : Measurable F) (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    Integrable (descend Λ F (descend_invariant_of_le hΛH hF)) νΛ ↔
      Integrable (descend H F hF) νH := by
  have hΛc : IsClosed (Λ : Set G) := Subgroup.isClosed_of_discreteTopology
  have : SecondCountableTopology Λ := TopologicalSpace.Subtype.secondCountableTopology (Λ : Set G)
  have : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasureOnCompacts (Measure.count : Measure Λ) :=
    ⟨fun _ hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete⟩
  have : (Measure.count : Measure Λ).IsOpenPosMeasure := ⟨fun _ _ hU => Measure.count_ne_zero hU⟩
  obtain ⟨ρ₀, -, hρ, -⟩ := exists_continuous_isNormalizingFunction Λ hΛc (Measure.count : Measure Λ)
  have hρH := hνΛ'.isNormalizingFunction_div_measure_univ hH hΛH hΛ' hfin hρ
  have hc : (νΛ' Set.univ).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨Measure.measure_univ_ne_zero.mpr hνΛ'.nonzero, hfin⟩
  rw [hνΛ.integrable_descend_iff hΛc hρ F hFm, hνH.integrable_descend_iff hH hρH F hFm hF]
  simp_rw [toReal_div_smul]
  exact (integrable_smul_iff (inv_ne_zero hc) _).symm

/-- **Quotients in stages, integral.** -/
theorem IsCompatible.integral_descend_eq_smul_of_le (hH : IsClosed (H : Set G)) (hΛH : Λ ≤ H)
    (hΛ' : ∀ x : H, x ∈ Λ' ↔ (x : G) ∈ Λ)
    (hνΛ : IsCompatible Λ μG Measure.count νΛ) (hνH : IsCompatible H μG μH νH)
    (hνΛ' : IsCompatible Λ' μH Measure.count νΛ') (hfin : νΛ' Set.univ ≠ ⊤)
    (F : G → E) (hFm : Measurable F) (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    ∫ q, descend Λ F (descend_invariant_of_le hΛH hF) q ∂νΛ =
      (νΛ' Set.univ).toReal • ∫ q, descend H F hF q ∂νH := by
  have hΛc : IsClosed (Λ : Set G) := Subgroup.isClosed_of_discreteTopology
  have : SecondCountableTopology Λ := TopologicalSpace.Subtype.secondCountableTopology (Λ : Set G)
  have : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasureOnCompacts (Measure.count : Measure Λ) :=
    ⟨fun _ hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete⟩
  have : (Measure.count : Measure Λ).IsOpenPosMeasure := ⟨fun _ _ hU => Measure.count_ne_zero hU⟩
  obtain ⟨ρ₀, -, hρ, -⟩ := exists_continuous_isNormalizingFunction Λ hΛc (Measure.count : Measure Λ)
  have hρH := hνΛ'.isNormalizingFunction_div_measure_univ hH hΛH hΛ' hfin hρ
  have hc : (νΛ' Set.univ).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨Measure.measure_univ_ne_zero.mpr hνΛ'.nonzero, hfin⟩
  rw [hνΛ.integral_descend_eq hΛc hρ F hFm, hνH.integral_descend_eq hH hρH F hFm hF]
  simp_rw [toReal_div_smul]
  rw [integral_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- **Quotients in stages** (complex form, `Λ ∩ H` written `Λ.subgroupOf H`). Let `H` be a closed
subgroup of `G` with a right-invariant measure `μH` finite on compacts, `Λ ≤ H` a discrete subgroup,
`νΛ`, `νH`, `νΛH` compatible with `(μG, count)`, `(μG, μH)`, `(μH, count)` on `Λ \ G`, `H \ G`,
`(Λ.subgroupOf H) \ H`, and `νΛH univ ≠ ⊤`. For a measurable left `H`-invariant `F : G → ℂ`, the
function descended to `Λ \ G` is `νΛ`-integrable exactly when the one descended to `H \ G` is
`νH`-integrable, and `∫_{Λ \ G} F dνΛ = (νΛH univ).toReal * ∫_{H \ G} F dνH`. -/
theorem IsCompatible.integral_descend_stages (hH : IsClosed (H : Set G)) (hΛH : Λ ≤ H)
    [MeasurableSpace (LeftQuotient (Λ.subgroupOf H))]
    [BorelSpace (LeftQuotient (Λ.subgroupOf H))]
    {νΛH : Measure (LeftQuotient (Λ.subgroupOf H))}
    (hνΛ : IsCompatible Λ μG Measure.count νΛ) (hνH : IsCompatible H μG μH νH)
    (hνΛH : IsCompatible (Λ.subgroupOf H) μH Measure.count νΛH) (hfin : νΛH Set.univ ≠ ⊤)
    (F : G → ℂ) (hFm : Measurable F) (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    (Integrable (descend Λ F (descend_invariant_of_le hΛH hF)) νΛ ↔
        Integrable (descend H F hF) νH) ∧
      ∫ q, descend Λ F (descend_invariant_of_le hΛH hF) q ∂νΛ =
        ((νΛH Set.univ).toReal : ℂ) * ∫ q, descend H F hF q ∂νH := by
  have hΛ' : ∀ x : H, x ∈ Λ.subgroupOf H ↔ (x : G) ∈ Λ := fun _ => Subgroup.mem_subgroupOf
  refine ⟨hνΛ.integrable_descend_iff_of_le hH hΛH hΛ' hνH hνΛH hfin F hFm hF, ?_⟩
  rw [hνΛ.integral_descend_eq_smul_of_le hH hΛH hΛ' hνH hνΛH hfin F hFm hF, Complex.real_smul]

end Langlands.QuotientIntegration
