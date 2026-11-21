import Langlands.Global.EisensteinConstantTerm.Core
import Langlands.Analysis.FundamentalDomainFibreAverage
import Langlands.Global.AdelicSubgroupHaarMeasure
import Langlands.Global.EisensteinConstantTerm.QuotientUnfolding
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Constant terms preserve integrals over a rational quotient

For a closed adelic subgroup `U(𝔸)` with compact rational quotient, and a discrete subgroup
`Λ` of `G(𝔸)` that contains `U(F)` and normalizes `U(F)` and `U(𝔸)`, the constant term along
`U` preserves the
integral of every left `Λ`-invariant nonnegative function over a fundamental domain of `Λ`.
This is the case `Λ = P₀(F)` of the Harish-Chandra decomposition in Bernstein–Lapid §7.3. -/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Function
open scoped ENNReal Pointwise

namespace Langlands.Global.ConstantTermAverage

section Haar

variable {V : Type*} [Group V] [TopologicalSpace V] [IsTopologicalGroup V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

/-- A right-invariant Haar measure on a second-countable locally compact group is invariant
under inversion. -/
theorem isInvInvariant_of_isMulRightInvariant (μ : Measure V) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have hsq : μ = c ^ 2 • μ := by
    have h := congrArg Measure.inv hc
    rw [Measure.inv_inv, Measure.inv_def (c • μ), Measure.map_smul, ← Measure.inv_def, hc,
      smul_smul, ← pow_two] at h
    · exact h
    · exact measurable_inv.aemeasurable
  have K : TopologicalSpace.PositiveCompacts V := Classical.arbitrary _
  have hpos := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin := K.isCompact.measure_lt_top (μ := μ) |>.ne
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [hsq]
    simp
  have : c ^ 2 = 1 ^ 2 := (ENNReal.mul_left_inj hpos hfin).mp h2
  have hc1 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective this
  rw [hc, hc1, one_smul]

/-- A topological automorphism that preserves a discrete subgroup with a fundamental domain of
finite positive Haar measure preserves Haar measure. -/
theorem measurePreserving_of_preserves_fundamentalDomain (μ : Measure V) [μ.IsHaarMeasure]
    (φ : V ≃ₜ* V) (Γ : Subgroup V) [Countable Γ] (hφΓ : ∀ w, w ∈ Γ ↔ φ w ∈ Γ)
    {C : Set V} (hCm : MeasurableSet C) (hC : IsFundamentalDomain Γ C μ) (hC0 : μ C ≠ 0)
    (hCtop : μ C ≠ ∞) : MeasurePreserving φ μ μ := by
  refine ⟨φ.continuous.measurable, ?_⟩
  let c : ℝ≥0∞ := Measure.haarScalarFactor (μ.map φ) μ
  have hc : μ.map φ = c • μ := Measure.isMulLeftInvariant_eq_smul (μ.map φ) μ
  have hqmp : Measure.QuasiMeasurePreserving φ μ μ := by
    refine ⟨φ.continuous.measurable, ?_⟩
    rw [hc]
    exact Measure.smul_absolutelyContinuous
  let e : Γ → Γ := fun γ => ⟨φ.symm γ, (hφΓ _).mpr (by simp)⟩
  have he : Bijective e := by
    refine ⟨fun γ γ' h => Subtype.ext ?_, fun γ => ⟨⟨φ γ, (hφΓ _).mp γ.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun x : Γ => φ (x : V)) h
      simpa [e] using this
    · simp [e]
  have hC' : IsFundamentalDomain Γ (φ ⁻¹' C) μ := by
    refine hC.preimage_of_equiv hqmp he fun γ x => ?_
    change φ (φ.symm γ * x) = (γ : V) * φ x
    simp
  have heq : μ (φ ⁻¹' C) = μ C := hC'.measure_eq hC
  have h1 : c * μ C = 1 * μ C := by
    have hm : μ.map φ C = μ (φ ⁻¹' C) := Measure.map_apply φ.continuous.measurable hCm
    rw [hc, Measure.smul_apply, smul_eq_mul] at hm
    rw [one_mul, hm, heq]
  have hc1 : c = 1 := (ENNReal.mul_left_inj hC0 hCtop).mp h1
  rw [hc, hc1, one_smul]

/-- Integrals of a `Γ`-invariant function over a fundamental domain are unchanged by an
automorphism that preserves `Γ` and the measure. -/
theorem setLIntegral_comp_symm_eq (ν : Measure V) (Γ : Subgroup V) [Countable Γ]
    [SMulInvariantMeasure Γ V ν] (c : V ≃ₜ* V)
    (hc : MeasurePreserving c ν ν) (hcs : MeasurePreserving c.symm ν ν)
    (hcΓ : ∀ w, w ∈ Γ ↔ c w ∈ Γ) {C : Set V} (hCm : MeasurableSet C)
    (hC : IsFundamentalDomain Γ C ν) {ψ : V → ℝ≥0∞} (hψ : Measurable ψ)
    (hψΓ : ∀ q : Γ, ∀ w, ψ (q • w) = ψ w) :
    ∫⁻ v in C, ψ (c.symm v) ∂ν = ∫⁻ w in C, ψ w ∂ν := by
  let C' : Set V := c ⁻¹' C
  have hC'm : MeasurableSet C' := hc.measurable hCm
  have hC' : IsFundamentalDomain Γ C' ν := by
    let e : Γ → Γ := fun q => ⟨c.symm q, by
      have := hcΓ (c.symm q)
      rw [ContinuousMulEquiv.apply_symm_apply] at this
      exact this.mpr q.2⟩
    have he : Bijective e := by
      refine ⟨fun q q' h => Subtype.ext ?_, fun q => ⟨⟨c q, (hcΓ q).mp q.2⟩, Subtype.ext ?_⟩⟩
      · have := congrArg (fun x : Γ => c (x : V)) h
        simpa [e] using this
      · simp [e]
    refine hC.preimage_of_equiv hc.quasiMeasurePreserving he fun q x => ?_
    change c (c.symm q * x) = (q : V) * c x
    simp
  calc ∫⁻ v in C, ψ (c.symm v) ∂ν = ∫⁻ v, C'.indicator ψ (c.symm v) ∂ν := by
        rw [← lintegral_indicator hCm]
        refine lintegral_congr fun v => ?_
        have hmem : v ∈ C ↔ c.symm v ∈ C' := by
          change v ∈ C ↔ c (c.symm v) ∈ C
          rw [ContinuousMulEquiv.apply_symm_apply]
        by_cases hv : v ∈ C
        · rw [indicator_of_mem hv, indicator_of_mem (hmem.mp hv)]
        · rw [indicator_of_notMem hv, indicator_of_notMem (fun h => hv (hmem.mpr h))]
    _ = ∫⁻ w in C', ψ w ∂ν := by
        rw [hcs.lintegral_comp (hψ.indicator hC'm), lintegral_indicator hC'm]
    _ = ∫⁻ w in C, ψ w ∂ν := hC'.setLIntegral_eq hC ψ hψΓ

end Haar

section Adelic

open scoped CategoryTheory.MonObj

open AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : Langlands.GroupScheme.SubgroupFunctor G)
  [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]

local instance adelicPointsLocallyCompactSpace : LocallyCompactSpace (adelicPoints F G U) :=
  hclosed.locallyCompactSpace

local instance rationalQuotientBorel : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

/-- The constant term along `U` of a nonnegative function, for the mass-one quotient measure
on `U(F) \ U(𝔸)`; for complex functions this is the integral of `subgroupConstantTerm`. -/
def lowerConstantTerm (f : AdelicGroupPoints F G → ℝ≥0∞) (g : AdelicGroupPoints F G) : ℝ≥0∞ :=
  ∫⁻ x, f (((Quotient.out x : adelicPoints F G U) : AdelicGroupPoints F G) * g)
    ∂normalizedRationalQuotientHaarMeasure F G U

/-- The chosen Borel fundamental domain of `U(F)` in `U(𝔸)`. -/
abbrev rationalFundamentalDomain : Set (adelicPoints F G U) :=
  LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U) (isDiscrete_rationalSubgroup F G U)

/-- Unfolded form of the constant term of a function that is invariant under `U(F)` on the
left. -/
theorem lowerConstantTerm_eq {f : AdelicGroupPoints F G → ℝ≥0∞} (hf : Measurable f)
    (g : AdelicGroupPoints F G)
    (hinv : ∀ q ∈ rationalSubgroup F G U, ∀ x : adelicPoints F G U,
      f (((q * x : adelicPoints F G U) : AdelicGroupPoints F G) * g) =
        f ((x : AdelicGroupPoints F G) * g)) :
    lowerConstantTerm F G U f g =
      ((Measure.haar : Measure (adelicPoints F G U)) (rationalFundamentalDomain F G U))⁻¹ *
        ∫⁻ v in rationalFundamentalDomain F G U, f ((v : AdelicGroupPoints F G) * g)
          ∂(Measure.haar : Measure (adelicPoints F G U)) := by
  have hm : Measurable fun v : adelicPoints F G U => f ((v : AdelicGroupPoints F G) * g) :=
    hf.comp (continuous_subtype_val.measurable.mul_const g)
  rw [lowerConstantTerm, normalizedRationalQuotientHaarMeasure, lintegral_smul_measure,
    Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_eq, quotientMassNormalizer]
  congr 1
  exact EisensteinConstantTerm.lintegral_out_eq (rationalSubgroup F G U) hm
    (fun q x => hinv q q.2 x) _ _

variable [CompactSpace (RationalQuotient F G U)]

section Normalized

variable (Λ : Subgroup (AdelicGroupPoints F G))
  (hΓ : (∀ w ∈ rationalSubgroup F G U, ((w : adelicPoints F G U) : AdelicGroupPoints F G) ∈ Λ) ∧
    ∀ l ∈ Λ, ∀ w ∈ rationalSubgroup F G U, ∃ w' ∈ rationalSubgroup F G U,
      ((w' : adelicPoints F G U) : AdelicGroupPoints F G) = l * w * l⁻¹)
  (hnorm : ∀ l ∈ Λ, ∀ w ∈ adelicPoints F G U, l * w * l⁻¹ ∈ adelicPoints F G U)

/-- Conjugation by `l ∈ Λ`, as a topological automorphism of `U(𝔸)`. -/
def conjEquiv (l : Λ) : adelicPoints F G U ≃ₜ* adelicPoints F G U where
  toFun w := ⟨l * w * (l : AdelicGroupPoints F G)⁻¹, hnorm l l.2 w w.2⟩
  invFun w := ⟨(l : AdelicGroupPoints F G)⁻¹ * w * l, by
    simpa using hnorm l⁻¹ (Λ.inv_mem l.2) w w.2⟩
  left_inv w := Subtype.ext (by simp [mul_assoc])
  right_inv w := Subtype.ext (by simp [mul_assoc])
  map_mul' w w' := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

@[simp]
theorem coe_conjEquiv (l : Λ) (w : adelicPoints F G U) :
    ((conjEquiv F G U Λ hnorm l w : adelicPoints F G U) : AdelicGroupPoints F G) =
      l * w * (l : AdelicGroupPoints F G)⁻¹ := rfl

include hΓ in
theorem mem_rationalSubgroup_conjEquiv_iff (l : Λ) (w : adelicPoints F G U) :
    w ∈ rationalSubgroup F G U ↔ conjEquiv F G U Λ hnorm l w ∈ rationalSubgroup F G U := by
  constructor
  · intro hw
    obtain ⟨w', hw', he⟩ := hΓ.2 l l.2 w hw
    have : conjEquiv F G U Λ hnorm l w = w' := Subtype.ext (by rw [coe_conjEquiv, he])
    rw [this]
    exact hw'
  · intro hw
    obtain ⟨w', hw', he⟩ := hΓ.2 (l : AdelicGroupPoints F G)⁻¹ (Λ.inv_mem l.2) _ hw
    have : w = w' := Subtype.ext (by rw [he, coe_conjEquiv]; group)
    rw [this]
    exact hw'

include hΓ in
/-- Conjugation by an element of `Λ` preserves Haar measure on `U(𝔸)`. -/
theorem measurePreserving_conjEquiv (l : Λ) :
    MeasurePreserving (conjEquiv F G U Λ hnorm l) Measure.haar Measure.haar := by
  have : Countable (rationalSubgroup F G U) :=
    LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_rationalSubgroup F G U)
  exact measurePreserving_of_preserves_fundamentalDomain Measure.haar (conjEquiv F G U Λ hnorm l)
    (rationalSubgroup F G U) (mem_rationalSubgroup_conjEquiv_iff F G U Λ hΓ hnorm l)
    (LeftCosetSpace.measurableSet_fundamentalDomain _ (isDiscrete_rationalSubgroup F G U))
    (LeftCosetSpace.isFundamentalDomain _ (isDiscrete_rationalSubgroup F G U) _)
    (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_zero U) (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_top U)

include hΓ in
private theorem invariance_of_Λ {f : AdelicGroupPoints F G → ℝ≥0∞}
    (hfΛ : ∀ l ∈ Λ, ∀ x, f (l * x) = f x) (g : AdelicGroupPoints F G) :
    ∀ q ∈ rationalSubgroup F G U, ∀ x : adelicPoints F G U,
      f (((q * x : adelicPoints F G U) : AdelicGroupPoints F G) * g) =
        f ((x : AdelicGroupPoints F G) * g) := by
  intro q hq x
  rw [Subgroup.coe_mul, mul_assoc]
  exact hfΛ _ (hΓ.1 q hq) _

omit [CompactSpace (RationalQuotient F G U)] in
@[simp]
theorem coe_conjEquiv_symm (l : Λ) (w : adelicPoints F G U) :
    (((conjEquiv F G U Λ hnorm l).symm w : adelicPoints F G U) : AdelicGroupPoints F G) =
      (l : AdelicGroupPoints F G)⁻¹ * w * l := rfl

include hΓ hnorm in
/-- **The constant term of a left `Λ`-invariant function is left `Λ`-invariant**, so it descends
to `Λ \ G(𝔸)`. -/
theorem lowerConstantTerm_mul_left {f : AdelicGroupPoints F G → ℝ≥0∞} (hf : Measurable f)
    (hfΛ : ∀ l ∈ Λ, ∀ x, f (l * x) = f x) (l : Λ) (g : AdelicGroupPoints F G) :
    lowerConstantTerm F G U f ((l : AdelicGroupPoints F G) * g) = lowerConstantTerm F G U f g := by
  have : Countable (rationalSubgroup F G U) :=
    LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_rationalSubgroup F G U)
  let c := conjEquiv F G U Λ hnorm l
  have hcs : MeasurePreserving c.symm Measure.haar Measure.haar := by
    refine measurePreserving_of_preserves_fundamentalDomain Measure.haar c.symm
      (rationalSubgroup F G U) (fun w => ?_)
      (LeftCosetSpace.measurableSet_fundamentalDomain _ (isDiscrete_rationalSubgroup F G U))
      (LeftCosetSpace.isFundamentalDomain _ (isDiscrete_rationalSubgroup F G U) _)
      (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_zero U) (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_top U)
    have := mem_rationalSubgroup_conjEquiv_iff F G U Λ hΓ hnorm l (c.symm w)
    rw [ContinuousMulEquiv.apply_symm_apply] at this
    exact this.symm
  let ψ : adelicPoints F G U → ℝ≥0∞ := fun w => f ((w : AdelicGroupPoints F G) * g)
  have hψ : Measurable ψ := hf.comp (continuous_subtype_val.measurable.mul_const g)
  rw [lowerConstantTerm_eq F G U hf (l * g) (invariance_of_Λ F G U Λ hΓ hfΛ (l * g)),
    lowerConstantTerm_eq F G U hf g (invariance_of_Λ F G U Λ hΓ hfΛ g)]
  congr 1
  calc ∫⁻ v in rationalFundamentalDomain F G U,
        f ((v : AdelicGroupPoints F G) * ((l : AdelicGroupPoints F G) * g)) ∂Measure.haar
      = ∫⁻ v in rationalFundamentalDomain F G U, ψ (c.symm v) ∂Measure.haar := by
        refine setLIntegral_congr_fun
          (LeftCosetSpace.measurableSet_fundamentalDomain _ (isDiscrete_rationalSubgroup F G U))
          fun v _ => ?_
        simp only [ψ, c, coe_conjEquiv_symm]
        rw [show (l : AdelicGroupPoints F G)⁻¹ * v * l * g =
          (l : AdelicGroupPoints F G)⁻¹ * (v * (l * g)) by group, hfΛ _ (Λ.inv_mem l.2)]
    _ = _ := setLIntegral_comp_symm_eq Measure.haar (rationalSubgroup F G U) c
        (measurePreserving_conjEquiv F G U Λ hΓ hnorm l) hcs
        (mem_rationalSubgroup_conjEquiv_iff F G U Λ hΓ hnorm l)
        (LeftCosetSpace.measurableSet_fundamentalDomain _ (isDiscrete_rationalSubgroup F G U))
        (LeftCosetSpace.isFundamentalDomain _ (isDiscrete_rationalSubgroup F G U) _) hψ
        (fun q w => invariance_of_Λ F G U Λ hΓ hfΛ g q q.2 w)

include hΓ hnorm in
/-- **The constant term preserves integrals over a fundamental domain of `Λ`.** Let `Λ` be a
discrete subgroup of `G(𝔸)` that contains `U(F)` and normalizes `U(F)` and `U(𝔸)`. Then for every
measurable left `Λ`-invariant `f ≥ 0`, integrating the constant term of `f` over a Borel
fundamental domain of `Λ` gives the integral of `f`. -/
theorem setLIntegral_lowerConstantTerm (hΛ : IsDiscrete (Λ : Set (AdelicGroupPoints F G)))
    {f : AdelicGroupPoints F G → ℝ≥0∞} (hf : Measurable f)
    (hfΛ : ∀ l ∈ Λ, ∀ x, f (l * x) = f x) :
    ∫⁻ g in LeftCosetSpace.fundamentalDomain Λ hΛ, lowerConstantTerm F G U f g ∂Measure.haar =
      ∫⁻ g in LeftCosetSpace.fundamentalDomain Λ hΛ, f g ∂Measure.haar := by
  let V := adelicPoints F G U
  let Γ := rationalSubgroup F G U
  let C := rationalFundamentalDomain F G U
  let ν : Measure V := Measure.haar
  have : Countable Λ := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
  have : ν.IsMulRightInvariant := haar_isMulRightInvariant_of_compactRationalQuotient F G U
  have : ν.IsInvInvariant := isInvInvariant_of_isMulRightInvariant ν
  have hCm : MeasurableSet C :=
    LeftCosetSpace.measurableSet_fundamentalDomain Γ (isDiscrete_rationalSubgroup F G U)
  have hC : IsFundamentalDomain Γ C ν :=
    LeftCosetSpace.isFundamentalDomain Γ (isDiscrete_rationalSubgroup F G U) ν
  have hfib := Langlands.Analysis.FibreAverage.setLIntegral_fibreAverage
    (Measure.haar : Measure (AdelicGroupPoints F G))
    Λ (LeftCosetSpace.fundamentalDomain Λ hΛ) (LeftCosetSpace.measurableSet_fundamentalDomain Λ hΛ)
    (LeftCosetSpace.fundamentalDomain_unique Λ hΛ) V.subtype continuous_subtype_val.measurable
    Subtype.val_injective Γ (fun w hw => hΓ.1 w hw) (fun l => conjEquiv F G U Λ hnorm l)
    (fun _ _ => rfl) (fun l w hw => (mem_rationalSubgroup_conjEquiv_iff F G U Λ hΓ hnorm l w).mp hw) ν
    (measurePreserving_conjEquiv F G U Λ hΓ hnorm) C hCm hC hf (fun l x => hfΛ l l.2 x)
  calc ∫⁻ g in LeftCosetSpace.fundamentalDomain Λ hΛ, lowerConstantTerm F G U f g ∂Measure.haar
      = ∫⁻ g in LeftCosetSpace.fundamentalDomain Λ hΛ, (ν C)⁻¹ *
          ∫⁻ v in C, f ((v : AdelicGroupPoints F G) * g) ∂ν ∂Measure.haar :=
        setLIntegral_congr_fun (LeftCosetSpace.measurableSet_fundamentalDomain Λ hΛ)
          fun g _ => lowerConstantTerm_eq F G U hf g (invariance_of_Λ F G U Λ hΓ hfΛ g)
    _ = (ν C)⁻¹ * ∫⁻ g in LeftCosetSpace.fundamentalDomain Λ hΛ,
          ∫⁻ v in C, f ((v : AdelicGroupPoints F G) * g) ∂ν ∂Measure.haar := by
        refine lintegral_const_mul _ ?_
        exact Measurable.lintegral_prod_left
          (hf.comp ((continuous_subtype_val.measurable.comp measurable_fst).mul measurable_snd))
    _ = (ν C)⁻¹ * (ν C * ∫⁻ g in LeftCosetSpace.fundamentalDomain Λ hΛ, f g ∂Measure.haar) := by
        rw [← hfib]
        rfl
    _ = _ := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_zero U)
          (Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_ne_top U), one_mul]

end Normalized

/-- **Statement form.** For a closed adelic subgroup `U(𝔸)` with compact rational quotient and
a discrete subgroup `Λ ≤ G(𝔸)` that normalizes `U(𝔸)`, contains `U(F)` and normalizes `U(F)`, the
nonnegative constant term along `U` of a measurable left `Λ`-invariant function is left
`Λ`-invariant and has the same integral over a Borel fundamental domain of `Λ`. -/
def AdelicConstantTermIntegralStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (U : Langlands.GroupScheme.SubgroupFunctor G)
    [IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
    [CompactSpace (RationalQuotient F G U)]
    (Λ : Subgroup (AdelicGroupPoints F G)) (hΛ : IsDiscrete (Λ : Set (AdelicGroupPoints F G))),
    (∀ w ∈ rationalSubgroup F G U, ((w : adelicPoints F G U) : AdelicGroupPoints F G) ∈ Λ) →
    (∀ l ∈ Λ, ∀ w ∈ rationalSubgroup F G U, ∃ w' ∈ rationalSubgroup F G U,
      ((w' : adelicPoints F G U) : AdelicGroupPoints F G) = l * w * l⁻¹) →
    (∀ l ∈ Λ, ∀ w ∈ adelicPoints F G U, l * w * l⁻¹ ∈ adelicPoints F G U) →
    ∀ {f : AdelicGroupPoints F G → ℝ≥0∞}, Measurable f → (∀ l ∈ Λ, ∀ x, f (l * x) = f x) →
      (∀ l ∈ Λ, ∀ g, lowerConstantTerm F G U f (l * g) = lowerConstantTerm F G U f g) ∧
      ∫⁻ g in LeftCosetSpace.fundamentalDomain Λ hΛ, lowerConstantTerm F G U f g ∂Measure.haar =
        ∫⁻ g in LeftCosetSpace.fundamentalDomain Λ hΛ, f g ∂Measure.haar

/-- Proof of `AdelicConstantTermIntegralStatement`. -/
theorem adelicConstantTermIntegral : AdelicConstantTermIntegralStatement.{u} := by
  intro F _ _ G _ _ U _ _ Λ hΛ hΓΛ hΓc hnorm f hf hfΛ
  have hΓ := And.intro hΓΛ hΓc
  exact ⟨fun l hl g => lowerConstantTerm_mul_left F G U Λ hΓ hnorm hf hfΛ ⟨l, hl⟩ g,
    setLIntegral_lowerConstantTerm F G U Λ hΓ hnorm hΛ hf hfΛ⟩

end Adelic

end Langlands.Global.ConstantTermAverage
