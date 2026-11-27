import Langlands.Global.CuspidalTestExpansion.StabilizerInvariance
import Langlands.Global.CuspidalTestExpansion.CosetTransfer
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicRepresentationHeightPropernessProof

/-! # Constant terms of stabilizer integrals along a larger unipotent group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  EisensteinConstantTerm RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (p : P ⟶ G)

section CosetSum

variable {V : GroupScheme (Spec (CommRingCat.of F))} (j : V ⟶ G)

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
local notation "Vᵣ" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j)

/-- The sum `x ↦ ∑_{γ ∈ (V(F) ∩ wP(F)w⁻¹) \ V(F)} Φ(w⁻¹ γ x)` over the rational stabilizer
cosets, evaluated at the chosen representatives. -/
def stabilizerCosetSum (w : AdelicGroupPoints F G) (Φ : AdelicGroupPoints F G → ℂ)
    (x : AdelicGroupPoints F G) : ℂ :=
  ∑' c : AmbientCosets Vᵣ (stabilizerRationalSubgroup F p j w),
    Φ (w⁻¹ * (((c.out : Vᵣ) : Vₐ) : AdelicGroupPoints F G) * x)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The stabilizer coset sum of a left `P(F)`-invariant function is left invariant under
`V(F)`. -/
theorem stabilizerCosetSum_mul_left (w : AdelicGroupPoints F G) (Φ : AdelicGroupPoints F G → ℂ)
    (hΦP : IsLeftInvariantUnder F G (rationalImage F p) Φ) (δ : Vₐ) (hδ : δ ∈ Vᵣ)
    (x : AdelicGroupPoints F G) :
    stabilizerCosetSum p j w Φ ((δ : AdelicGroupPoints F G) * x) =
      stabilizerCosetSum p j w Φ x := by
  let g' : Vₐ → ℂ := fun a => Φ (w⁻¹ * (a : AdelicGroupPoints F G) * x)
  have hg : ∀ z ∈ stabilizerRationalSubgroup F p j w, ∀ a, g' (z * a) = g' a := by
    intro z hz a
    have hz' := ((mem_stabilizerRationalSubgroup_iff F p j w z).mp hz).2
    change Φ (w⁻¹ * ((z * a : Vₐ) : AdelicGroupPoints F G) * x) =
      Φ (w⁻¹ * (a : AdelicGroupPoints F G) * x)
    rw [show w⁻¹ * ((z * a : Vₐ) : AdelicGroupPoints F G) * x =
        (w⁻¹ * (z : AdelicGroupPoints F G) * w) * (w⁻¹ * (a : AdelicGroupPoints F G) * x) by
      simp only [Subgroup.coe_mul]; group]
    exact hΦP _ hz' _
  unfold stabilizerCosetSum
  calc ∑' c : AmbientCosets Vᵣ (stabilizerRationalSubgroup F p j w),
        Φ (w⁻¹ * (((c.out : Vᵣ) : Vₐ) : AdelicGroupPoints F G) * ((δ : AdelicGroupPoints F G) * x))
      = ∑' c : AmbientCosets Vᵣ (stabilizerRationalSubgroup F p j w),
          g' (((c.out : Vᵣ) : Vₐ) * (δ * 1)) := tsum_congr fun c => by
        simp only [g', mul_one, Subgroup.coe_mul, mul_assoc]
    _ = ∑' c : AmbientCosets Vᵣ (stabilizerRationalSubgroup F p j w),
          g' (((c.out : Vᵣ) : Vₐ) * 1) := tsum_out_mul_left hg hδ 1
    _ = _ := tsum_congr fun c => by simp only [g', mul_one]

theorem measurable_stabilizerCosetSum (w : AdelicGroupPoints F G) {Φ : AdelicGroupPoints F G → ℂ}
    (hΦc : Continuous Φ) : Measurable (stabilizerCosetSum p j w Φ) := by
  have : Countable Vᵣ := countable_rationalSubgroup _
  exact Measurable.tsum fun c => (hΦc.comp (continuous_const.mul continuous_id)).measurable

omit [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 1600000 in
/-- Let `0 < N`, `w` rational and `Φ` continuous and left invariant under `P(F)`, with a summable
nonnegative majorant `‖Φ(γ_c g)‖ ≤ b c · H(g)^d` (`d ≥ 0`) over `P(F) \ G(F)`. Then the
stabilizer coset sum is continuous: by the `P(F)`-invariance its terms are values of `Φ` at
distinct cosets of `P(F) \ G(F)`, so they are dominated by distinct terms of the majorant. -/
theorem continuous_stabilizerCosetSum {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (w : AdelicGroupPoints F G) (hw : w ∈ rationalSubgroup F G) {Φ : AdelicGroupPoints F G → ℂ}
    (hΦc : Continuous Φ) (hΦP : IsLeftInvariantUnder F G (rationalImage F p) Φ)
    (b : ParabolicRationalCosets F p → ℝ) (d : ℝ) (hb : Summable b) (hb0 : ∀ c, 0 ≤ b c)
    (hd : 0 ≤ d)
    (hbound : ∀ (g : AdelicGroupPoints F G) (c : ParabolicRationalCosets F p),
      ‖Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * g)‖ ≤
        b c * adelicHeight F G rho g ^ d) :
    Continuous (stabilizerCosetSum p j w Φ) := by
  classical
  set Λ := stabilizerRationalSubgroup F p j w
  have hr : ∀ c : AmbientCosets Vᵣ Λ,
      w⁻¹ * (((c.out : Vᵣ) : Vₐ) : AdelicGroupPoints F G) ∈ rationalSubgroup F G := fun c =>
    mul_mem (inv_mem hw)
      (rationalImage_le_rationalSubgroup j ((mem_rationalSubgroup_range_iff j _).mp (c.out).2))
  let κ : AmbientCosets Vᵣ Λ → ParabolicRationalCosets F p := fun c =>
    Quotient.mk _ (⟨_, hr c⟩ : rationalSubgroup F G)
  have hκ : ∀ c x, Φ (w⁻¹ * (((c.out : Vᵣ) : Vₐ) : AdelicGroupPoints F G) * x) =
      Φ ((((κ c).out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) := by
    intro c x
    have h : QuotientGroup.rightRel (parabolicRationalSubgroup F p) (κ c).out
        (⟨_, hr c⟩ : rationalSubgroup F G) := Quotient.exact (Quotient.out_eq (κ c))
    have h' := QuotientGroup.rightRel_apply.mp h
    have h'' : (((⟨_, hr c⟩ : rationalSubgroup F G) * ((κ c).out)⁻¹ : rationalSubgroup F G) :
        AdelicGroupPoints F G) ∈ rationalImage F p := by
      rw [rationalImage_eq_map]
      exact h'
    have := hΦP _ h'' ((((κ c).out : rationalSubgroup F G) : AdelicGroupPoints F G) * x)
    rw [← this]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    rw [inv_mul_cancel_left]
  have hκinj : Function.Injective κ := by
    intro c c' hcc
    have h := Quotient.exact hcc
    change QuotientGroup.rightRel _ _ _ at h
    rw [QuotientGroup.rightRel_apply, parabolicRationalSubgroup, Subgroup.mem_subgroupOf,
      ← rationalImage_eq_map] at h
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    apply Quotient.sound
    show QuotientGroup.rightRel _ c.out c'.out
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, mem_stabilizerRationalSubgroup_iff]
    refine ⟨Subgroup.mul_mem _ c'.out.2 (Subgroup.inv_mem _ c.out.2), ?_⟩
    convert h using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hsum : Summable (b ∘ κ) := hb.comp_injective hκinj
  have hHc := continuous_adelicHeight F G rho hN
  rw [continuous_iff_continuousAt]
  intro x₀
  set M := adelicHeight F G rho x₀ + 1
  have hU : {x | adelicHeight F G rho x < M} ∈ nhds x₀ :=
    (isOpen_lt hHc continuous_const).mem_nhds
      (show adelicHeight F G rho x₀ < M from lt_add_one _)
  have hon : ContinuousOn (stabilizerCosetSum p j w Φ) {x | adelicHeight F G rho x < M} := by
    unfold stabilizerCosetSum
    refine continuousOn_tsum (fun c => (hΦc.comp (continuous_const.mul continuous_id)).continuousOn)
      (hsum.mul_right (M ^ d)) fun c x hx => ?_
    rw [hκ c x]
    refine (hbound x (κ c)).trans ?_
    have hH0 : 0 ≤ adelicHeight F G rho x := zero_le_one.trans (one_le_adelicHeight F G rho hN x)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hH0 (le_of_lt hx) hd) (hb0 _)
  exact hon.continuousAt hU

end CosetSum

section Unfold

variable {Q V : GroupScheme (Spec (CommRingCat.of F))} (q : Q ⟶ G) (iV : V ⟶ Q)
  [IsAffine V.X.left] [IsClosedImmersion (iV ≫ q).hom.hom.left]

set_option maxHeartbeats 1600000 in
/-- Let `V` be normal in `Q`, with compact rational quotient `V(F) \ V(𝔸)`, and let `Φ` be
continuous and left invariant under `P(F)`. At an argument `z` where the stabilizer integrand is
integrable, the stabilizer integral is the constant term along `V` of the stabilizer coset sum
(unfolding of `(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)` over `V(F) \ V(𝔸)`). -/
theorem stabilizerIntegral_eq_subgroupConstantTerm
    (hN : (SubgroupFunctor.range iV).IsNormal)
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iV ≫ q)))]
    (w : AdelicGroupPoints F G) {Φ : AdelicGroupPoints F G → ℂ} (hΦc : Continuous Φ)
    (hΦP : IsLeftInvariantUnder F G (rationalImage F p) Φ) (z : AdelicGroupPoints F G)
    (hint : Integrable (eisensteinStabilizerIntegrand p q iV w Φ z)
      (stabilizerMeasure F p (iV ≫ q) w)) :
    stabilizerIntegral p q iV w Φ z =
      subgroupConstantTerm F (iV ≫ q) (stabilizerCosetSum p (iV ≫ q) w Φ) z := by
  classical
  set Γ := AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q))
  set Λ := stabilizerRationalSubgroup F p (iV ≫ q) w
  have : Countable Γ := countable_rationalSubgroup _
  let ρ' : AmbientCosets Γ Λ →
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) :=
    fun c => (c.out : Γ)
  have hρΓ : ∀ c, ρ' c ∈ Γ := fun c => (c.out).2
  have hρ : ∀ δ ∈ Γ, ∃! c, δ * (ρ' c)⁻¹ ∈ Λ := fun δ hδ =>
    RankinSelbergGlobal.Unfolding.existsUnique_cosetRep Λ Γ δ hδ
  have h1 : map F Q G q (rational F Q 1) = 1 := by rw [map_one, map_one]
  obtain ⟨hL, hI⟩ := unfold_conj (p := p) (q := q) (iV := iV) hN w 1 1 h1 ρ' hρΓ hρ hΦc hΦP z
  have hfin := hint.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfin
  have hfin' : (∫⁻ v in LeftCosetSpace.fundamentalDomain Γ
        (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G _),
      ∑' ν, ‖Φ (w⁻¹ * (ρ' ν : AdelicGroupPoints F G) * 1 *
        ((v : AdelicGroupPoints F G) * z))‖ₑ
      ∂AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))) ≠ ∞ := by
    rw [← hL]
    simp only [one_mul]
    exact hfin.ne
  have h2 := hI hfin'
  simp only [one_mul, mul_one] at h2
  have hfm : Measurable fun v : AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (iV ≫ q)) =>
      stabilizerCosetSum p (iV ≫ q) w Φ ((v : AdelicGroupPoints F G) * z) :=
    (measurable_stabilizerCosetSum p (iV ≫ q) w hΦc).comp
      (continuous_subtype_val.mul continuous_const).measurable
  have hf : ∀ (t : Γ) (x : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))),
      stabilizerCosetSum p (iV ≫ q) w Φ ((((t : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV ≫ q))) * x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * z) =
        stabilizerCosetSum p (iV ≫ q) w Φ ((x : AdelicGroupPoints F G) * z) := by
    intro t x
    rw [Subgroup.coe_mul, mul_assoc]
    exact stabilizerCosetSum_mul_left p (iV ≫ q) w Φ hΦP t t.2 _
  unfold stabilizerIntegral subgroupConstantTerm
  rw [normalizedRationalQuotientHaarMeasure_eq_quotientMeasure,
    RankinSelbergGlobal.Unfolding.integral_out_eq Γ hfm hf]
  exact h2

end Unfold

section Transitivity

variable {U V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left] [IsAffine V.X.left]
  (jU : U ⟶ G) (jV : V ⟶ G) [IsClosedImmersion jU.hom.hom.left] [IsClosedImmersion jV.hom.hom.left]

set_option maxHeartbeats 1600000 in
/-- For `U ≤ V` with `U` normalized by `V` and compact rational quotients, the constant term along
`V` of the constant term along `U` of a continuous function that is left invariant under `V(F)`
is its constant term along `V`. -/
theorem subgroupConstantTerm_subgroupConstantTerm_of_le
    (h : SubgroupFunctor.range jU ≤ SubgroupFunctor.range jV)
    (hUV : (SubgroupFunctor.range jU).IsNormalizedBy (SubgroupFunctor.range jV))
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range jU))]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range jV))]
    (f : AdelicGroupPoints F G → ℂ) (hfc : Continuous f)
    (hf : ∀ δ ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range jV),
      ∀ x, f ((δ : AdelicGroupPoints F G) * x) = f x)
    (g : AdelicGroupPoints F G) :
    subgroupConstantTerm F jV (subgroupConstantTerm F jU f) g = subgroupConstantTerm F jV f g := by
  classical
  open AdelicSubgroupPoints in
  set UF := SubgroupFunctor.range jU
  set VF := SubgroupFunctor.range jV
  have hUc : IsClosed (AdelicSubgroupPoints.adelicPoints F G UF : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G jU
  have hVc : IsClosed (AdelicSubgroupPoints.adelicPoints F G VF : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G jV
  have : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G VF) := hVc.locallyCompactSpace
  have : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G UF) := hUc.locallyCompactSpace
  have : BorelSpace (AdelicSubgroupPoints.RationalQuotient F G UF) :=
    AdelicSubgroupPoints.rationalQuotientBorelSpace F G UF
  have : BorelSpace (AdelicSubgroupPoints.RationalQuotient F G VF) :=
    AdelicSubgroupPoints.rationalQuotientBorelSpace F G VF
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G VF
  let Δ := AdelicSubgroupPoints.rationalSubgroup F G UF
  let jj := AdelicSubgroupPoints.adelicInclusion F G h
  let mU := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G UF
  let mV := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G VF
  let φ₀ : AdelicSubgroupPoints.adelicPoints F G VF → ℂ :=
    fun n => f ((n : AdelicGroupPoints F G) * g)
  have hInv : ∀ (t : Γ) (n : AdelicSubgroupPoints.adelicPoints F G VF),
      φ₀ ((t : AdelicSubgroupPoints.adelicPoints F G VF) * n) = φ₀ n := by
    intro t n
    simp only [φ₀, Subgroup.coe_mul, mul_assoc]
    exact hf _ t.2 _
  let fG : AdelicSubgroupPoints.RationalQuotient F G VF → ℂ := LeftCosetSpace.lift Γ φ₀ hInv
  have hfGc : Continuous fG :=
    LeftCosetSpace.continuous_lift Γ φ₀ hInv (hfc.comp (continuous_subtype_val.mul continuous_const))
  have hΓ : IsDiscrete (Γ : Set (AdelicSubgroupPoints.adelicPoints F G VF)) :=
    AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G VF
  have : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  have : (Measure.count : Measure Γ).IsHaarMeasure := by
    have := LeftCosetSpace.isFiniteMeasureOnCompacts_count Γ hΓ
    exact { toIsOpenPosMeasure := ⟨fun _ _ hs => Measure.count_ne_zero hs⟩ }
  have : IsProbabilityMeasure mU :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G UF
  have : IsProbabilityMeasure mV :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G VF
  have : mV.Regular :=
    (AdelicSubgroupPoints.compactCompatibleNormalizedRationalQuotientMeasure F G VF).property.2.regular
  have hj : Δ ≤ Γ.comap jj := AdelicSubgroupPoints.rationalSubgroup_le_comap_adelicInclusion F G h
  have hjc : Continuous jj := continuous_subtype_val.subtype_mk _
  have hconj := LeftCosetSpace.subgroupAverageConjugation Γ Δ jj hj mU (by
    rintro ⟨_, q, rfl⟩
    let a := AdelicSubgroupPoints.adelicNormalizerConj F G hUV
      (AdelicSubgroupPoints.rational F G VF q⁻¹)
    have ha := AdelicSubgroupPoints.adelicNormalizerConj_mem_rationalSubgroup_iff F G hUV q⁻¹
    refine ⟨a, ha, AdelicSubgroupPoints.measurePreserving_rationalQuotientAutomorphism F G UF a ha,
      fun n => ?_⟩
    apply Subtype.ext
    change (a n : AdelicGroupPoints F G) =
      (AdelicSubgroupPoints.rational F G VF q : AdelicGroupPoints F G)⁻¹ * n *
        (AdelicSubgroupPoints.rational F G VF q : AdelicGroupPoints F G)
    simp [a])
  have hi := LeftCosetSpace.integral_compactSubgroupAverage Γ Δ jj hj hjc mU hconj
    (Γ.isClosed_of_isDiscrete hΓ) Measure.count mV
    (measurePreserving_rightTranslate_of_compactRationalQuotient F G VF) hfGc
  have hR : subgroupConstantTerm F jV f g = ∫ x, fG x ∂mV := by
    unfold subgroupConstantTerm
    exact congrArg (fun ψ => ∫ x, ψ x ∂mV) (RankinSelbergGlobal.Unfolding.out_eq_lift Γ φ₀ hInv)
  have hL : subgroupConstantTerm F jV (subgroupConstantTerm F jU f) g =
      ∫ x, LeftCosetSpace.compactSubgroupAverage Γ Δ jj hj mU hconj fG x ∂mV := by
    unfold subgroupConstantTerm
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun x => ?_
    have hx : LeftCosetSpace.mk Γ (Quotient.out x) = x := Quotient.out_eq x
    rw [← hx, LeftCosetSpace.compactSubgroupAverage_mk, hx]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun y => ?_
    obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective Δ y
    rw [LeftCosetSpace.subgroupFiberEval_mk]
    have hδ : n * ((LeftCosetSpace.mk Δ n).out)⁻¹ ∈ Δ :=
      (LeftCosetSpace.mk_eq_mk_iff Δ _ _).mp (Quotient.out_eq _)
    have ho : (((LeftCosetSpace.mk Δ n).out : AdelicSubgroupPoints.adelicPoints F G UF) :
          AdelicGroupPoints F G) =
        ((jj (n * ((LeftCosetSpace.mk Δ n).out)⁻¹)⁻¹ :
          AdelicSubgroupPoints.adelicPoints F G VF) : AdelicGroupPoints F G) *
          (n : AdelicGroupPoints F G) := by
      simp only [jj, AdelicSubgroupPoints.adelicInclusion_coe, Subgroup.coe_inv,
        Subgroup.coe_mul, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    change f ((((LeftCosetSpace.mk Δ n).out : AdelicSubgroupPoints.adelicPoints F G UF) :
        AdelicGroupPoints F G) * (((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G VF) :
          AdelicGroupPoints F G) * g)) =
      f (((jj n * Quotient.out x : AdelicSubgroupPoints.adelicPoints F G VF) :
        AdelicGroupPoints F G) * g)
    rw [ho, mul_assoc, hf _ (hj (Δ.inv_mem hδ)) _]
    simp only [jj, AdelicSubgroupPoints.adelicInclusion_coe, Subgroup.coe_mul, mul_assoc]
  rw [hL, hi, hR]

end Transitivity

section Compare

variable {UQ UJ : GroupScheme (Spec (CommRingCat.of F))} (jQ : UQ ⟶ G) (jJ : UJ ⟶ G)

local notation "Qₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range jQ)
local notation "Jₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range jJ)
local notation "Qᵣ" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range jQ)
local notation "Jᵣ" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range jJ)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Let `Φ` be left invariant under `P(F)` (the rational image of `p`). If `U_Q ≤ U_J` and every
rational point of `U_J` is a point of the stabilizer `U_J(F) ∩ wP(F)w⁻¹` times a rational point
of `U_Q`, the stabilizer coset sums of `Φ` along `U_Q` and along `U_J` agree: the inclusion
induces a bijection of the coset spaces, and the left `P(F)`-invariance of `Φ` makes the
summands independent of the chosen coset representatives. -/
theorem stabilizerCosetSum_eq_of_le (h : SubgroupFunctor.range jQ ≤ SubgroupFunctor.range jJ)
    (w : AdelicGroupPoints F G) (Φ : AdelicGroupPoints F G → ℂ)
    (hΦP : IsLeftInvariantUnder F G (rationalImage F p) Φ)
    (hdec : ∀ δ ∈ Jᵣ, ∃ a ∈ stabilizerRationalSubgroup F p jJ w, ∃ t : Qₐ, t ∈ Qᵣ ∧
      (δ : AdelicGroupPoints F G) = (a : AdelicGroupPoints F G) * (t : AdelicGroupPoints F G))
    (x : AdelicGroupPoints F G) :
    stabilizerCosetSum p jQ w Φ x = stabilizerCosetSum p jJ w Φ x := by
  classical
  let φ : Qᵣ →* Jₐ := (AdelicSubgroupPoints.adelicInclusion F G h).comp (Qᵣ).subtype
  have hφB : ∀ y, φ y ∈ Jᵣ := fun y =>
    AdelicSubgroupPoints.rationalSubgroup_le_comap_adelicInclusion F G h y.2
  have hpre : ∀ y, φ y ∈ stabilizerRationalSubgroup F p jJ w ↔
      y ∈ (stabilizerRationalSubgroup F p jQ w).subgroupOf Qᵣ := by
    intro y
    rw [Subgroup.mem_subgroupOf, mem_stabilizerRationalSubgroup_iff,
      mem_stabilizerRationalSubgroup_iff]
    exact ⟨fun hh => ⟨y.2, hh.2⟩, fun hh => ⟨hφB y, hh.2⟩⟩
  have hsurj : ∀ b ∈ Jᵣ, ∃ a ∈ stabilizerRationalSubgroup F p jJ w, ∃ y, b = a * φ y := by
    intro b hb
    obtain ⟨a, ha, t, ht, hbt⟩ := hdec b hb
    exact ⟨a, ha, ⟨t, ht⟩, Subtype.ext hbt⟩
  let f : Jₐ → ℂ := fun a => Φ (w⁻¹ * (a : AdelicGroupPoints F G) * x)
  have hf : ∀ a ∈ stabilizerRationalSubgroup F p jJ w, ∀ y, f (a * y) = f y := by
    intro a ha y
    have ha' := ((mem_stabilizerRationalSubgroup_iff F p jJ w a).mp ha).2
    change Φ (w⁻¹ * ((a * y : Jₐ) : AdelicGroupPoints F G) * x) =
      Φ (w⁻¹ * (y : AdelicGroupPoints F G) * x)
    rw [show w⁻¹ * ((a * y : Jₐ) : AdelicGroupPoints F G) * x =
        (w⁻¹ * (a : AdelicGroupPoints F G) * w) * (w⁻¹ * (y : AdelicGroupPoints F G) * x) by
      simp only [Subgroup.coe_mul]; group]
    exact hΦP _ ha' _
  have key := CosetTransfer.tsum_cosetEquiv φ ((stabilizerRationalSubgroup F p jQ w).subgroupOf Qᵣ)
    (stabilizerRationalSubgroup F p jJ w) Jᵣ hφB hpre hsurj f hf 1
  have e1 : ∀ c : AmbientCosets Qᵣ (stabilizerRationalSubgroup F p jQ w),
      f (φ c.out * 1) = Φ (w⁻¹ * (((c.out : Qᵣ) : Qₐ) : AdelicGroupPoints F G) * x) := fun c => by
    simp only [f, φ, mul_one, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      AdelicSubgroupPoints.adelicInclusion_coe]
  have e2 : ∀ c : AmbientCosets Jᵣ (stabilizerRationalSubgroup F p jJ w),
      f (((c.out : Jᵣ) : Jₐ) * 1) = Φ (w⁻¹ * (((c.out : Jᵣ) : Jₐ) : AdelicGroupPoints F G) * x) :=
    fun c => by simp only [f, mul_one]
  unfold stabilizerCosetSum
  rw [← tsum_congr e1, ← tsum_congr e2]
  exact key

end Compare

section Main

variable {QQ VQ QJ VJ : GroupScheme (Spec (CommRingCat.of F))}
  (qQ : QQ ⟶ G) (iVQ : VQ ⟶ QQ) (qJ : QJ ⟶ G) (iVJ : VJ ⟶ QJ)
  [IsAffine VQ.X.left] [IsAffine VJ.X.left]
  [IsClosedImmersion (iVQ ≫ qQ).hom.hom.left] [IsClosedImmersion (iVJ ≫ qJ).hom.hom.left]

set_option maxHeartbeats 1600000 in
/-- **Constant terms of stabilizer integrals.** Let `U_Q = iVQ ≫ qQ` and `U_J = iVJ ≫ qJ` be
closed subgroups, normal in `Q_Q` resp. `Q_J`, with compact rational quotients, such that
`U_Q ≤ U_J` and `U_Q` is normalized by `U_J`. Let `w` be rational and suppose
`U_J(F) ⊆ (U_J(F) ∩ wP(F)w⁻¹) U_Q(F)`. Let `0 < N` and let `Φ` be continuous and left
`P(F)`-invariant with a summable nonnegative majorant `‖Φ(γ_c g)‖ ≤ b c · H(g)^d` (`d ≥ 0`) over
`P(F) \ G(F)`. If the stabilizer integrand along `U_Q` is integrable at every argument and the
one along `U_J` at `y`, then the constant term along `U_J` of the stabilizer integral over
`(U_Q(F) ∩ wP(F)w⁻¹) \ U_Q(𝔸)`, evaluated at `y`, is the stabilizer integral over
`(U_J(F) ∩ wP(F)w⁻¹) \ U_J(𝔸)` at `y`. -/
theorem subgroupConstantTerm_stabilizerIntegral_of_le
    (hNQ : (SubgroupFunctor.range iVQ).IsNormal) (hNJ : (SubgroupFunctor.range iVJ).IsNormal)
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iVQ ≫ qQ)))]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iVJ ≫ qJ)))]
    (hle : SubgroupFunctor.range (iVQ ≫ qQ) ≤ SubgroupFunctor.range (iVJ ≫ qJ))
    (hnorm : (SubgroupFunctor.range (iVQ ≫ qQ)).IsNormalizedBy (SubgroupFunctor.range (iVJ ≫ qJ)))
    (w : AdelicGroupPoints F G) (hw : w ∈ rationalSubgroup F G)
    (hdec : ∀ δ ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iVJ ≫ qJ)),
      ∃ a ∈ stabilizerRationalSubgroup F p (iVJ ≫ qJ) w,
        ∃ t : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iVQ ≫ qQ)),
          t ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iVQ ≫ qQ)) ∧
          (δ : AdelicGroupPoints F G) = (a : AdelicGroupPoints F G) * (t : AdelicGroupPoints F G))
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    {Φ : AdelicGroupPoints F G → ℂ} (hΦc : Continuous Φ)
    (hΦP : IsLeftInvariantUnder F G (rationalImage F p) Φ)
    (b : ParabolicRationalCosets F p → ℝ) (d : ℝ) (hb : Summable b) (hb0 : ∀ c, 0 ≤ b c)
    (hd : 0 ≤ d)
    (hbound : ∀ (g : AdelicGroupPoints F G) (c : ParabolicRationalCosets F p),
      ‖Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * g)‖ ≤
        b c * adelicHeight F G rho g ^ d)
    (hintQ : ∀ z, Integrable (eisensteinStabilizerIntegrand p qQ iVQ w Φ z)
      (stabilizerMeasure F p (iVQ ≫ qQ) w))
    (y : AdelicGroupPoints F G)
    (hintJ : Integrable (eisensteinStabilizerIntegrand p qJ iVJ w Φ y)
      (stabilizerMeasure F p (iVJ ≫ qJ) w)) :
    subgroupConstantTerm F (iVJ ≫ qJ) (stabilizerIntegral p qQ iVQ w Φ) y =
      stabilizerIntegral p qJ iVJ w Φ y := by
  have hQ : stabilizerIntegral p qQ iVQ w Φ =
      subgroupConstantTerm F (iVQ ≫ qQ) (stabilizerCosetSum p (iVQ ≫ qQ) w Φ) := funext fun z =>
    stabilizerIntegral_eq_subgroupConstantTerm p qQ iVQ hNQ w hΦc hΦP z (hintQ z)
  have hFeq : stabilizerCosetSum p (iVQ ≫ qQ) w Φ = stabilizerCosetSum p (iVJ ≫ qJ) w Φ :=
    funext fun x => stabilizerCosetSum_eq_of_le p (iVQ ≫ qQ) (iVJ ≫ qJ) hle w Φ hΦP hdec x
  have hFc := continuous_stabilizerCosetSum p (iVQ ≫ qQ) rho hN w hw hΦc hΦP b d hb hb0 hd hbound
  have hFinv : ∀ δ ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iVJ ≫ qJ)),
      ∀ x, stabilizerCosetSum p (iVQ ≫ qQ) w Φ ((δ : AdelicGroupPoints F G) * x) =
        stabilizerCosetSum p (iVQ ≫ qQ) w Φ x := by
    intro δ hδ x
    rw [hFeq]
    exact stabilizerCosetSum_mul_left p (iVJ ≫ qJ) w Φ hΦP δ hδ x
  rw [hQ, subgroupConstantTerm_subgroupConstantTerm_of_le (iVQ ≫ qQ) (iVJ ≫ qJ) hle hnorm _ hFc
    hFinv y, hFeq,
    ← stabilizerIntegral_eq_subgroupConstantTerm p qJ iVJ hNJ w hΦc hΦP y hintJ]

end Main

end Langlands.Global
