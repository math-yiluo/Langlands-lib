import Langlands.Global.EisensteinConstantTerm.UnfoldingRight

/-! # The unfolding identity of the geometric lemma for abstract locally compact groups -/

noncomputable section

universe u

open MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

open Langlands.QuotientIntegration

attribute [local instance] locallyCompactSpace_of_isClosed_subgroup
  secondCountableTopology_subgroup isClosed_conjStab

variable {𝒢 : Type u} [Group 𝒢] [TopologicalSpace 𝒢] [IsTopologicalGroup 𝒢] [T2Space 𝒢]
  [LocallyCompactSpace 𝒢] [SecondCountableTopology 𝒢] [MeasurableSpace 𝒢] [BorelSpace 𝒢]

/-- Averages of left `Δ`-invariant functions over the chosen fundamental domain are invariant
under right translation, when one compact set meets every orbit of `Δ` (so that the normalized
Haar measure is right invariant). -/
theorem setIntegral_fundamentalDomain_mul_right {X : Type*} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (Δ : Subgroup X) (hΔ : IsDiscrete (Δ : Set X))
    {K : Set X} (hK : IsCompact K) (hKcover : ∀ x, ∃ γ ∈ Δ, γ * x ∈ K)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : X → E)
    (hg : ∀ γ ∈ Δ, ∀ x, g (γ * x) = g x) (x₀ : X) :
    ∫ x in fundamentalDomain Δ hΔ, g (x * x₀) ∂normalizedHaar Δ hΔ =
      ∫ x in fundamentalDomain Δ hΔ, g x ∂normalizedHaar Δ hΔ := by
  have := isMulRightInvariant_normalizedHaar Δ hΔ hK hKcover
  have : Countable Δ := countable_of_isDiscrete Δ hΔ
  have hmp : MeasurePreserving (· * x₀) (normalizedHaar Δ hΔ) (normalizedHaar Δ hΔ) :=
    measurePreserving_mul_right _ x₀
  have hemb : MeasurableEmbedding (· * x₀ : X → X) :=
    (Homeomorph.mulRight x₀).measurableEmbedding
  set s := (· * x₀⁻¹) ⁻¹' fundamentalDomain Δ hΔ
  have hpre : (· * x₀) ⁻¹' s = fundamentalDomain Δ hΔ := by ext x; simp [s]
  have hsm : MeasurableSet s :=
    (measurable_mul_const x₀⁻¹) (measurableSet_fundamentalDomain Δ hΔ)
  have hsu : ∀ x, ∃! γ : Δ, (γ : X) * x ∈ s := by
    intro x
    obtain ⟨γ, hγ, hu⟩ := fundamentalDomain_unique Δ hΔ (x * x₀⁻¹)
    refine ⟨γ, by simpa [s, mul_assoc] using hγ, fun δ hδ => hu δ ?_⟩
    simpa [s, mul_assoc] using hδ
  calc ∫ x in fundamentalDomain Δ hΔ, g (x * x₀) ∂normalizedHaar Δ hΔ
      = ∫ x in (· * x₀) ⁻¹' s, g (x * x₀) ∂normalizedHaar Δ hΔ := by rw [hpre]
    _ = ∫ y in s, g y ∂normalizedHaar Δ hΔ := hmp.setIntegral_preimage_emb hemb g s
    _ = _ :=
      (IsFundamentalDomain.mk' (μ := normalizedHaar Δ hΔ) hsm.nullMeasurableSet hsu).setIntegral_eq
        (isFundamentalDomain Δ hΔ _) (fun γ x => hg _ γ.property x)

omit [T2Space 𝒢] [LocallyCompactSpace 𝒢] in
/-- For an s-finite measure on a subgroup, averages over a set of left translates of a measurable
function are measurable functions. -/
theorem measurable_setIntegral_subgroup_mul (X : Subgroup 𝒢) (μ : Measure X) [SFinite μ]
    (s : Set X) (h : 𝒢 → ℂ) (hm : Measurable h) :
    Measurable (fun x : 𝒢 => ∫ u in s, h (u.val * x) ∂μ) := by
  have : StronglyMeasurable (fun x : 𝒢 => ∫ u in s, h (u.val * x) ∂μ) := by
    apply MeasureTheory.StronglyMeasurable.integral_prod_right
    exact (hm.comp ((continuous_subtype_val.comp continuous_snd).mul
      continuous_fst).measurable).stronglyMeasurable
  exact this.measurable

omit [T2Space 𝒢] in
/-- When one compact set meets every orbit of `U' ∩ R` in `U'`, the normalized average over
`(U' ∩ R) \ U'` of a function left invariant under `U' ∩ R` is left invariant under `U'`. -/
theorem setIntegral_latticeOf_mul_left (R : Subgroup 𝒢) (hR : IsDiscrete (R : Set 𝒢))
    (U' : Subgroup 𝒢) [IsClosed (U' : Set 𝒢)]
    {CU' : Set U'} (hCU' : IsCompact CU') (hCU'c : ∀ k, ∃ γ ∈ latticeOf R U', γ * k ∈ CU')
    (h : 𝒢 → ℂ) (hhR : ∀ z ∈ U', z ∈ R → ∀ x, h (z * x) = h x) {u : 𝒢} (hu : u ∈ U') (x : 𝒢) :
    ∫ z in fundamentalDomain (latticeOf R U') (isDiscrete_latticeOf R hR U'), h (z.val * (u * x))
        ∂normalizedHaar (latticeOf R U') (isDiscrete_latticeOf R hR U') =
      ∫ z in fundamentalDomain (latticeOf R U') (isDiscrete_latticeOf R hR U'), h (z.val * x)
        ∂normalizedHaar (latticeOf R U') (isDiscrete_latticeOf R hR U') := by
  have := setIntegral_fundamentalDomain_mul_right (latticeOf R U') (isDiscrete_latticeOf R hR U')
    hCU' hCU'c (fun z : U' => h (z.val * x))
    (fun γ hγ z => by
      change h ((γ.val * z.val) * x) = h (z.val * x)
      rw [mul_assoc]; exact hhR _ γ.property hγ _) ⟨u, hu⟩
  simp only [Subgroup.coe_mul, mul_assoc] at this
  exact this

section Main

variable (R : Subgroup 𝒢) (hR : IsDiscrete (R : Set 𝒢))
  (V V' U U' A B : Subgroup 𝒢) [IsClosed (V : Set 𝒢)] [IsClosed (V' : Set 𝒢)]
  [IsClosed (U : Set 𝒢)] [IsClosed (U' : Set 𝒢)] [IsClosed (A : Set 𝒢)] [IsClosed (B : Set 𝒢)]
  (w : 𝒢) (hw : w ∈ R)
  (hUU' : U ≤ U') (hAU' : A ≤ U') (hAV : ∀ a ∈ A, w * a * w⁻¹ ∈ V)
  (hUn : ∀ x ∈ U', ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hAU : ∀ a ∈ A, a ∈ U → a = 1)
  (hdecU : ∀ x ∈ U', ∃ u ∈ U, ∃ a ∈ A, u * a = x)
  (hratU : ∀ x ∈ U', x ∈ R → ∀ u ∈ U, ∀ a ∈ A, u * a = x → a ∈ R)
  (hVV' : V ≤ V') (hBV' : B ≤ V') (hBU : ∀ b ∈ B, w⁻¹ * b * w ∈ U)
  (hVn : ∀ x ∈ V', ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hBV : ∀ b ∈ B, b ∈ V → b = 1)
  (hdecV : ∀ x ∈ V', ∃ v ∈ V, ∃ b ∈ B, v * b = x)
  (hratV : ∀ x ∈ V', x ∈ R → ∀ v ∈ V, ∀ b ∈ B, v * b = x → b ∈ R)

include hR hw hUU' hAU' hAV hUn hAU hdecU hratU hVV' hBV' hBU hVn hBV hdecV hratV in
/-- **The unfolding identity of the geometric lemma, abstract form.** Let `R` be a discrete
subgroup of the locally compact second countable group `𝒢`, `w ∈ R`, and let `V ≤ V'`,
`U ≤ U'`, `A`, `B` be closed subgroups with closed semidirect decompositions `U' = U ⋊ A` and
`V' = V ⋊ B` compatible with `R`, such that `w A w⁻¹ ⊆ V` and `w⁻¹ B w ⊆ U`. Suppose one
compact set meets every orbit of the intersection with `R` of each of `V`, `V'`, `U`, `U'`,
`V ∩ w U w⁻¹` and `V ∩ w U' w⁻¹`. Normalize all Haar measures by their intersections with `R`
and put `C h (x) = ∫_{(U' ∩ R) \ U'} h(u x) du`, computed on the chosen fundamental domain.
If `h` is measurable and left invariant under `U` and `U' ∩ R`, and `v ↦ h(w⁻¹ v y)` has finite
absolute integral over the fundamental domain of `V ∩ R ∩ w U' w⁻¹` in `V`, then
`x ↦ C h (w⁻¹ x y)` is integrable over the fundamental domain of `V' ∩ R ∩ w U' w⁻¹` in `V'`, and
the two integrals are equal. -/
theorem integral_unfolding_eq
    {CV : Set V} (hCV : IsCompact CV) (hCVc : ∀ k, ∃ γ ∈ latticeOf R V, γ * k ∈ CV)
    {CV' : Set V'} (hCV' : IsCompact CV') (hCV'c : ∀ k, ∃ γ ∈ latticeOf R V', γ * k ∈ CV')
    {CU : Set U} (hCU : IsCompact CU) (hCUc : ∀ k, ∃ γ ∈ latticeOf R U, γ * k ∈ CU)
    {CU' : Set U'} (hCU' : IsCompact CU') (hCU'c : ∀ k, ∃ γ ∈ latticeOf R U', γ * k ∈ CU')
    {CK : Set (conjStab V U w)} (hCK : IsCompact CK)
    (hCKc : ∀ k, ∃ γ ∈ conjStabLattice R V w U, γ * k ∈ CK)
    {CN : Set (conjStab V U' w)} (hCN : IsCompact CN)
    (hCNc : ∀ k, ∃ γ ∈ conjStabLattice R V w U', γ * k ∈ CN)
    [MeasurableSpace (LeftQuotient (conjStab V U' w))]
    [BorelSpace (LeftQuotient (conjStab V U' w))]
    (h : 𝒢 → ℂ) (hm : Measurable h) (hhU : ∀ u ∈ U, ∀ x, h (u * x) = h x)
    (hhR : ∀ z ∈ U', z ∈ R → ∀ x, h (z * x) = h x) (y : 𝒢)
    (hfin : ∫⁻ v in fundamentalDomain (latticeOf R V ⊓ conjStab V U' w)
        ((isDiscrete_latticeOf R hR V).mono inf_le_left), ‖h (w⁻¹ * v.val * y)‖ₑ
        ∂normalizedHaar (latticeOf R V) (isDiscrete_latticeOf R hR V) < ∞) :
    IntegrableOn (fun x : V' => ∫ u in fundamentalDomain (latticeOf R U')
          (isDiscrete_latticeOf R hR U'), h (u.val * (w⁻¹ * x.val * y))
          ∂normalizedHaar (latticeOf R U') (isDiscrete_latticeOf R hR U'))
        (fundamentalDomain (latticeOf R V' ⊓ conjStab V' U' w)
          ((isDiscrete_latticeOf R hR V').mono inf_le_left))
        (normalizedHaar (latticeOf R V') (isDiscrete_latticeOf R hR V')) ∧
      ∫ x in fundamentalDomain (latticeOf R V' ⊓ conjStab V' U' w)
          ((isDiscrete_latticeOf R hR V').mono inf_le_left),
          (∫ u in fundamentalDomain (latticeOf R U') (isDiscrete_latticeOf R hR U'),
            h (u.val * (w⁻¹ * x.val * y))
            ∂normalizedHaar (latticeOf R U') (isDiscrete_latticeOf R hR U'))
          ∂normalizedHaar (latticeOf R V') (isDiscrete_latticeOf R hR V') =
        ∫ v in fundamentalDomain (latticeOf R V ⊓ conjStab V U' w)
          ((isDiscrete_latticeOf R hR V).mono inf_le_left), h (w⁻¹ * v.val * y)
          ∂normalizedHaar (latticeOf R V) (isDiscrete_latticeOf R hR V) := by
  have hVd := isDiscrete_latticeOf R hR V
  have hU'd := isDiscrete_latticeOf R hR U'
  have hNd := isDiscrete_conjStabLattice R hR V w U'
  set μV := normalizedHaar (latticeOf R V) hVd
  set μN := normalizedHaar (conjStabLattice R V w U') hNd
  set μU' := normalizedHaar (latticeOf R U') hU'd
  have : μV.IsHaarMeasure := isHaarMeasure_normalizedHaar _ hVd hCV hCVc
  have : μV.Regular := regular_normalizedHaar _ hVd
  have : μV.IsMulRightInvariant := isMulRightInvariant_normalizedHaar _ hVd hCV hCVc
  have : μN.IsHaarMeasure := isHaarMeasure_normalizedHaar _ hNd hCN hCNc
  have : μN.Regular := regular_normalizedHaar _ hNd
  have : μN.IsMulRightInvariant := isMulRightInvariant_normalizedHaar _ hNd hCN hCNc
  obtain ⟨ν, hν⟩ := compatibleMeasureExists (conjStab V U' w) (isClosed_conjStab V U' w) μV μN
  set Γ₀ := latticeOf R V ⊓ conjStab V U' w
  have hΓ₀d : IsDiscrete (Γ₀ : Set V) := hVd.mono inf_le_left
  let C : 𝒢 → ℂ := fun x => ∫ u in fundamentalDomain (latticeOf R U') hU'd, h (u.val * x) ∂μU'
  -- the left side
  let f : V → ℂ := fun v => h (w⁻¹ * v.val * y)
  have hfm : Measurable f :=
    hm.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hfΓ : ∀ γ ∈ Γ₀, ∀ v, f (γ * v) = f v := by
    intro γ hγ v
    have hγU : w⁻¹ * γ.val * w ∈ U' := (mem_conjStab γ).mp hγ.2
    have hγR : w⁻¹ * γ.val * w ∈ R := (conj_mem_iff hw _).mpr hγ.1
    change h (w⁻¹ * (γ.val * v.val) * y) = h (w⁻¹ * v.val * y)
    rw [show w⁻¹ * (γ.val * v.val) * y = (w⁻¹ * γ.val * w) * (w⁻¹ * v.val * y) by group]
    exact hhR _ hγU hγR _
  have hfint : IntegrableOn f (fundamentalDomain Γ₀ hΓ₀d) μV :=
    ⟨hfm.aestronglyMeasurable, hfin⟩
  have : Countable (Γ₀.comap (conjStab V U' w).subtype) := countable_of_isDiscrete _ hNd
  obtain ⟨hint1, heq1⟩ := integral_transversal_eq (conjStab V U' w) (isClosed_conjStab V U' w)
    μN μV ν hν Γ₀ inf_le_right (measurableSet_fundamentalDomain Γ₀ hΓ₀d)
    (fundamentalDomain_unique Γ₀ hΓ₀d) (isFundamentalDomain (conjStabLattice R V w U') hNd μN)
    f hfm.stronglyMeasurable hfΓ hfint
  have hslice : ∀ v : V, ∫ a in fundamentalDomain (conjStabLattice R V w U') hNd,
      f (a.val * v) ∂μN = C (w⁻¹ * v.val * y) := by
    intro v
    show _ = ∫ u in fundamentalDomain (latticeOf R U') hU'd, h (u.val * (w⁻¹ * v.val * y)) ∂μU'
    rw [setIntegral_inner_eq R hR V U U' A w hw hUU' hAU' hAV hUn hAU hdecU hratU hCU hCUc
      hCU' hCU'c hCK hCKc hCN hCNc h hhU hhR (w⁻¹ * v.val * y)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change h (w⁻¹ * (a.val.val * v.val) * y) = h (w⁻¹ * a.val.val * w * (w⁻¹ * v.val * y))
    congr 1
    group
  -- the right side
  have hCinv : ∀ u ∈ U', ∀ x, C (u * x) = C x := by
    intro u hu x
    have := setIntegral_fundamentalDomain_mul_right (latticeOf R U') hU'd hCU' hCU'c
      (fun z : U' => h (z.val * x))
      (fun γ hγ z => by
        change h ((γ.val * z.val) * x) = h (z.val * x)
        rw [mul_assoc]; exact hhR _ γ.property hγ _) ⟨u, hu⟩
    change ∫ z in _, h (z.val * (u * x)) ∂μU' = ∫ z in _, h (z.val * x) ∂μU'
    simp only [Subgroup.coe_mul, mul_assoc] at this
    exact this
  have hCm : Measurable C := by
    have : StronglyMeasurable C := by
      apply MeasureTheory.StronglyMeasurable.integral_prod_right
      exact (hm.comp ((continuous_subtype_val.comp continuous_snd).mul
        continuous_fst).measurable).stronglyMeasurable
    exact this.measurable
  let Φ : V' → ℂ := fun x => C (w⁻¹ * x.val * y)
  have hΦm : Measurable Φ :=
    hCm.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hΦN : ∀ n ∈ conjStab V' U' w, ∀ x, Φ (n * x) = Φ x := by
    intro n hn x
    change C (w⁻¹ * (n.val * x.val) * y) = C (w⁻¹ * x.val * y)
    rw [show w⁻¹ * (n.val * x.val) * y = (w⁻¹ * n.val * w) * (w⁻¹ * x.val * y) by group]
    exact hCinv _ ((mem_conjStab n).mp hn) _
  have hint2 : Integrable (fun q => Φ (Subgroup.inclusion hVV' (Quotient.out q))) ν := by
    have : (fun q : LeftQuotient (conjStab V U' w) =>
        Φ (Subgroup.inclusion hVV' (Quotient.out q))) =
        fun q => ∫ a in fundamentalDomain (conjStabLattice R V w U') hNd,
          f (a.val * Quotient.out q) ∂μN := by
      funext q
      exact (hslice (Quotient.out q)).symm
    rw [this]
    exact hint1
  obtain ⟨hI, hE⟩ := integral_rightTransversal_eq R hR V V' U' B w hVV' hBV'
    (fun b hb => hUU' (hBU b hb)) hratV hVn hBV hdecV hCV hCVc hCV' hCV'c hCN hCNc μN rfl ν hν
    Φ hΦm hΦN hint2
  refine ⟨hI, ?_⟩
  change ∫ x in _, Φ x ∂_ = _
  rw [hE, heq1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  exact (hslice (Quotient.out q)).symm

end Main

end Langlands.Global.LeftCosetSpace
