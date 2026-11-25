import Langlands.TraceFormula.TwistedOrbital
import Langlands.Analysis.Local.QuotientL2UnfoldingProof
import Langlands.Representation.Unitary.IntegratedTranslationPointwiseProof
import Langlands.Analysis.HilbertSchmidtIntegralKernel
import Langlands.Analysis.TraceClassHilbertSchmidtProof

/-!
# `R(f) ∘ I_θ` as an integral operator on `Γ \ G`

Let `G` be a Hausdorff, locally compact, second countable group with a left Haar measure `μG`,
`Γ` a discrete subgroup, `ν` a measure on `Γ \ G` compatible with `μG` and the counting measure on
`Γ` (`IsCompatible Γ μG Measure.count ν`), `θ` a continuous automorphism of `G` with `θ Γ = Γ` whose
induced homeomorphism `θ̄` of `Γ \ G` preserves `ν`, `π` the right regular representation on
`L²(Γ \ G, ν)` and `f ∈ C_c(G, ℂ)`. Write `R(f) = integratedIsometricAction μG π … f …` and
`I_θ = twistOperator Γ θ hθΓ ν hθν` (`I_θ φ = φ ∘ θ̄⁻¹`).

* `twistedQuotientKernel Γ θ hθ f` is the twisted kernel `K(x, y) = Σ_{γ ∈ Γ} f(x⁻¹ γ θ(y))`
  (`twistedKernel`) descended to `Γ \ G × Γ \ G`; on the diagonal it is `twistedKernelDiagonal`
  (`twistedQuotientKernel_self`).
* For compact `A, B ⊆ G` only finitely many `γ` give a nonzero term with `x ∈ A`, `y ∈ B`
  (`finite_twistedKernel_support`), so `K` is continuous on `G × G`
  (`continuous_uncurry_twistedKernel`) and on `Γ \ G × Γ \ G`
  (`continuous_uncurry_twistedQuotientKernel`). The row of `Γ x` vanishes off the image of the
  compact set `θ⁻¹(x · supp f)` (`twistedQuotientKernel_mk_eq_zero`), so every row is in `Lᵖ(ν)`
  (`memLp_twistedQuotientKernel_row`).
* `R(f) ∘ I_θ` is the integral operator with kernel `K`: for every `φ ∈ L²(Γ \ G, ν)`,
  `(R(f) I_θ φ)(q) = ∫ K(q, q') φ(q') dν(q')` for `ν`-almost every `q`
  (`twistedKernelOperator_ae_eq`). The pointwise form is `integral_mul_twistOperator_eq`, through
  the `L²` vector of `quotientL2Unfolding` and the invariance of `ν` under `θ̄`.
* If `R(f) ∘ I_θ` is Hilbert–Schmidt, in particular if it is trace class, then
  `K ∈ L²(Γ \ G × Γ \ G, ν × ν)` (`memLp_uncurry_twistedQuotientKernel_of_isHilbertSchmidt`,
  `memLp_uncurry_twistedQuotientKernel`), by `memLp_uncurry_of_isHilbertSchmidt`. No compactness of
  `Γ \ G` is assumed.

Neither the right invariance of `μG` nor the invariance of `μG` under `θ` is used.

Getz–Hahn 2024, §18.5 (the kernel `K_f(g, θ(h))` of `R(f) ∘ I_θ`); Bourbaki, *Intégration*,
Chapter VII, §2 (quotient measures).
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory Filter Topology
open Langlands.QuotientIntegration
open scoped CompactlySupported ComplexConjugate ENNReal
open Langlands.Analysis.OperatorIdeals

universe u uF

section Descent

variable {G : Type u} [Group G] {F : Type uF} [FunLike F G G] [MonoidHomClass F G G]

/-- The twisted kernel descended to `Γ \ G × Γ \ G`. -/
def twistedQuotientKernel (Γ : Subgroup G) (θ : F) (hθ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : G → ℂ) :
    LeftQuotient Γ → LeftQuotient Γ → ℂ :=
  Quotient.lift₂ (twistedKernel Γ θ f) (by
    intro x₁ y₁ x₂ y₂ hx hy
    have hx' : x₂ * x₁⁻¹ ∈ Γ := QuotientGroup.rightRel_apply.mp hx
    have hy' : y₂ * y₁⁻¹ ∈ Γ := QuotientGroup.rightRel_apply.mp hy
    calc twistedKernel Γ θ f x₁ y₁
        = twistedKernel Γ θ f ((⟨x₂ * x₁⁻¹, hx'⟩ : Γ).val * x₁)
            ((⟨y₂ * y₁⁻¹, hy'⟩ : Γ).val * y₁) := by
          rw [twistedKernel_left_mul_left, twistedKernel_left_mul_right Γ θ f hθ]
      _ = twistedKernel Γ θ f x₂ y₂ := by simp)

@[simp] theorem twistedQuotientKernel_mk (Γ : Subgroup G) (θ : F) (hθ : ∀ γ ∈ Γ, θ γ ∈ Γ)
    (f : G → ℂ) (x y : G) :
    twistedQuotientKernel Γ θ hθ f (Quotient.mk _ x) (Quotient.mk _ y) =
      twistedKernel Γ θ f x y := rfl

theorem twistedQuotientKernel_self (Γ : Subgroup G) (θ : F) (hθ : ∀ γ ∈ Γ, θ γ ∈ Γ)
    (f : G → ℂ) (q : LeftQuotient Γ) :
    twistedQuotientKernel Γ θ hθ f q q = twistedKernelDiagonal Γ θ hθ f q := by
  induction q using Quotient.inductionOn with
  | h x => rfl

end Descent

section Topology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  {F : Type uF} [FunLike F G G] [MonoidHomClass F G G]

omit [MonoidHomClass F G G] in
/-- Only finitely many `γ ∈ Γ` give a nonvanishing term `f (x⁻¹ γ θ y)` with `x, y` in given
compact sets. -/
theorem finite_twistedKernel_support (Γ : Subgroup G) [DiscreteTopology Γ] (θ : F)
    (hθ : Continuous θ) (f : C_c(G, ℂ)) {A B : Set G} (hA : IsCompact A) (hB : IsCompact B) :
    {γ : Γ | ∃ x ∈ A, ∃ y ∈ B, f (x⁻¹ * γ * θ y) ≠ 0}.Finite := by
  have hK : IsCompact ((fun p : G × G × G => p.1 * p.2.1 * (θ p.2.2)⁻¹) ''
      (A ×ˢ (tsupport f ×ˢ B))) :=
    (hA.prod (f.hasCompactSupport.prod hB)).image
      ((continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
        (hθ.comp (continuous_snd.comp continuous_snd)).inv)
  have ht := Γ.tendsto_coe_cofinite_of_isDiscrete
    (SetLike.isDiscrete_iff_discreteTopology.mpr ‹_›)
  have hfin := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, Filter.mem_cofinite] at hfin
  refine hfin.subset ?_
  rintro γ ⟨x, hx, y, hy, hf⟩
  simp only [Set.mem_compl_iff, Set.mem_preimage, not_not]
  exact ⟨(x, x⁻¹ * γ * θ y, y), ⟨hx, subset_tsupport _ hf, hy⟩, by simp [mul_assoc]⟩

omit [MonoidHomClass F G G] in
/-- The sum defining the twisted kernel has finitely many nonzero terms at each point. -/
theorem hasFiniteSupport_twistedKernel_terms (Γ : Subgroup G) [DiscreteTopology Γ] (θ : F)
    (hθ : Continuous θ) (f : C_c(G, ℂ)) (x y : G) :
    Function.HasFiniteSupport (fun γ : Γ => f (x⁻¹ * γ * θ y)) := by
  refine (finite_twistedKernel_support Γ θ hθ f (A := {x}) (B := {y}) isCompact_singleton
    isCompact_singleton).subset ?_
  intro γ hγ
  exact ⟨x, rfl, y, rfl, hγ⟩

omit [MonoidHomClass F G G] in
/-- The twisted kernel is continuous on `G × G`: near each point it is a finite sum. -/
theorem continuous_uncurry_twistedKernel [LocallyCompactSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (θ : F) (hθ : Continuous θ) (f : C_c(G, ℂ)) :
    Continuous (Function.uncurry (twistedKernel Γ θ (f : G → ℂ))) := by
  have hc : ∀ γ : Γ, Continuous fun p : G × G => f (p.1⁻¹ * γ * θ p.2) := fun γ =>
    f.continuous.comp ((continuous_fst.inv.mul continuous_const).mul (hθ.comp continuous_snd))
  have hlf : LocallyFinite fun γ : Γ =>
      Function.support fun p : G × G => f (p.1⁻¹ * γ * θ p.2) := by
    intro p
    obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds p.1
    obtain ⟨B, hBc, hB⟩ := exists_compact_mem_nhds p.2
    refine ⟨A ×ˢ B, prod_mem_nhds hA hB, (finite_twistedKernel_support Γ θ hθ f hAc hBc).subset ?_⟩
    rintro γ ⟨z, hz, hzAB⟩
    exact ⟨z.1, hzAB.1, z.2, hzAB.2, hz⟩
  have heq : Function.uncurry (twistedKernel Γ θ (f : G → ℂ)) =
      fun p : G × G => ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * θ p.2) := by
    funext p
    exact tsum_eq_finsum (hasFiniteSupport_twistedKernel_terms Γ θ hθ f p.1 p.2)
  rw [heq]
  exact continuous_finsum hc hlf

/-- The descended kernel is continuous on `Γ \ G × Γ \ G`. -/
theorem continuous_uncurry_twistedQuotientKernel [LocallyCompactSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (θ : F) (hθ : Continuous θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : C_c(G, ℂ)) :
    Continuous (Function.uncurry (twistedQuotientKernel Γ θ hθΓ (f : G → ℂ))) := by
  have hq := leftQuotient_isOpenQuotientMap Γ
  rw [(hq.prodMap hq).isQuotientMap.continuous_iff]
  exact continuous_uncurry_twistedKernel Γ θ hθ f

omit [IsTopologicalGroup G] [T2Space G] in
/-- Each row `q' ↦ K(Γ x, q')` of the descended kernel vanishes off the image in `Γ \ G` of the
compact set `θ⁻¹(x · supp f)`. -/
theorem twistedQuotientKernel_mk_eq_zero (Γ : Subgroup G) (θ : G ≃ₜ* G)
    (hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ) (f : G → ℂ) (x : G) (q : LeftQuotient Γ)
    (hq : q ∉ leftQuotientMap Γ '' (θ.symm '' ((fun c => x * c) '' tsupport f))) :
    twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) f (Quotient.mk _ x) q = 0 := by
  induction q using Quotient.inductionOn with
  | h y =>
    rw [twistedQuotientKernel_mk, twistedKernel]
    refine (tsum_congr fun γ => ?_).trans tsum_zero
    by_contra hne
    apply hq
    have hγ' : θ.symm (γ : G)⁻¹ ∈ Γ := by
      rw [← hθΓ, ContinuousMulEquiv.apply_symm_apply]
      exact Γ.inv_mem γ.2
    refine ⟨θ.symm (x * (x⁻¹ * γ * θ y)), ⟨x * (x⁻¹ * γ * θ y),
      ⟨x⁻¹ * γ * θ y, subset_tsupport _ hne, rfl⟩, rfl⟩, ?_⟩
    apply Quotient.sound
    change QuotientGroup.rightRel Γ _ y
    rw [QuotientGroup.rightRel_apply]
    have : y * (θ.symm (x * (x⁻¹ * γ * θ y)))⁻¹ = θ.symm (γ : G)⁻¹ := by
      apply θ.injective
      simp [mul_assoc]
    rw [this]
    exact hγ'

end Topology

section Analysis

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G]
  [BorelSpace G] in
private theorem countable_of_discreteTopology (Γ : Subgroup G) [DiscreteTopology Γ] :
    Countable Γ := by
  have : SecondCountableTopology Γ :=
    TopologicalSpace.Subtype.secondCountableTopology (Γ : Set G)
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem integral_count_eq_tsum {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] {g : α → ℂ} (hg : Function.HasFiniteSupport g) :
    ∫ a, g a ∂Measure.count = ∑' a, g a := by
  have hs : Function.HasFiniteSupport (fun a => ‖g a‖) := by
    refine Set.Finite.subset hg fun a ha => ?_
    simpa using ha
  rw [integral_countable (integrable_count_iff.2 (summable_of_hasFiniteSupport hs))]
  refine tsum_congr fun a => ?_
  simp [Measure.real]

omit [LocallyCompactSpace G] in
/-- The orbit average for the counting measure of `b ↦ conj f (x⁻¹ b)` at `Γ θ(y)` is the
conjugate of the twisted kernel at `(x, y)`. -/
theorem quotientAverage_count_star_eq (Γ : Subgroup G) [DiscreteTopology Γ]
    {F : Type uF} [FunLike F G G] (θ : F) (hθ : Continuous θ) (f : C_c(G, ℂ)) (x y : G) :
    quotientAverage Γ Measure.count (fun b => star (f (x⁻¹ * b))) (Quotient.mk _ (θ y)) =
      star (twistedKernel Γ θ (f : G → ℂ) x y) := by
  have : Countable Γ := countable_of_discreteTopology Γ
  rw [quotientAverage_mk, twistedKernel, tsum_star]
  have hfin := hasFiniteSupport_twistedKernel_terms Γ θ hθ f x y
  rw [integral_count_eq_tsum]
  · simp only [mul_assoc]
  · refine Set.Finite.subset hfin fun γ hγ => ?_
    simp only [Function.mem_support, ne_eq, star_eq_zero] at hγ ⊢
    simpa [mul_assoc] using hγ


/-- **The pairing behind the kernel.** For `x ∈ G` and `φ ∈ L²(Γ \ G, ν)`,
`∫_G f(a) (I_θ φ)(Γ x a) dμG(a) = ∫_{Γ \ G} K(Γ x, q) φ(q) dν(q)`. -/
theorem integral_mul_twistOperator_eq (μG : Measure G) [μG.IsHaarMeasure]
    (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : G ≃ₜ* G) (hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ)
    (hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν)
    (f : C_c(G, ℂ)) (x : G) (φ : Lp ℂ 2 ν) :
    ∫ a, f a * (twistOperator Γ θ hθΓ ν hθν φ : LeftQuotient Γ → ℂ) (Quotient.mk _ (x * a)) ∂μG =
      ∫ q, twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) (Quotient.mk _ x) q *
        φ q ∂ν := by
  have hΓc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  have : Countable Γ := countable_of_discreteTopology Γ
  have : ν.Regular := hν.regular
  have : IsFiniteMeasureOnCompacts (Measure.count : Measure Γ) :=
    ⟨fun _ hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete⟩
  let k : C_c(G, ℂ) :=
    { toFun := fun b => star (f (x⁻¹ * b))
      continuous_toFun := (f.continuous.comp (continuous_const.mul continuous_id)).star
      hasCompactSupport' :=
        (f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft x⁻¹)).comp_left
          (star_zero _) }
  have hk : ∀ b, k b = star (f (x⁻¹ * b)) := fun _ => rfl
  obtain ⟨-, -, v, _ℓ, hvA, hvφ⟩ := quotientL2Unfolding Γ hΓc Measure.count μG ν hν k
  let θq := quotientAutomorphism Γ θ hθΓ
  let ψ := twistOperator Γ θ hθΓ ν hθν φ
  -- `∫ f(a) ψ(Γ x a) da = ⟪v, ψ⟫`, by left invariance of `μG`.
  have ha : ∫ a, f a * ψ (Quotient.mk _ (x * a)) ∂μG = inner ℂ v ψ := by
    rw [(hvφ ψ).2.2, ← integral_mul_left_eq_self
      (fun g => star (k g) * ψ (leftQuotientMap Γ g)) x]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [hk, star_star, inv_mul_cancel_left]
    rfl
  -- `θ̄⁻¹` and `θ̄` preserve `ν`.
  let e : LeftQuotient Γ ≃ᵐ LeftQuotient Γ := θq.symm.toMeasurableEquiv
  have he : MeasurePreserving e ν ν := by
    simpa only [e, Homeomorph.toMeasurableEquiv_coe] using hθν
  have hθq : MeasurePreserving θq ν ν := by
    simpa only [e, Homeomorph.toMeasurableEquiv_symm_coe, Homeomorph.symm_symm] using he.symm e
  -- `⟪v, ψ⟫ = ∫ φ(p) conj (v (θ̄ p)) dν(p)`.
  have hb : inner ℂ v ψ = ∫ p, φ p * conj (v (θq p)) ∂ν := by
    rw [L2.inner_def]
    calc ∫ q, inner ℂ (v q) (ψ q) ∂ν = ∫ q, φ (θq.symm q) * conj (v q) ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [twistOperator_coeFn Γ θ hθΓ ν hθν φ] with q hq
          rw [RCLike.inner_apply, hq]
      _ = ∫ q, (fun p => φ p * conj (v (θq p))) (e q) ∂ν := by
          refine integral_congr_ae (Eventually.of_forall fun q => ?_)
          simp [e]
      _ = ∫ p, φ p * conj (v (θq p)) ∂ν :=
          he.integral_comp' (fun p => φ p * conj (v (θq p)))
  -- `v ∘ θ̄` is almost everywhere the conjugate kernel row.
  have hd : (fun p => v (θq p)) =ᵐ[ν] fun p => quotientAverage Γ Measure.count k (θq p) :=
    hθq.quasiMeasurePreserving.ae_eq_comp hvA
  have hpt : ∀ p, φ p * conj (quotientAverage Γ Measure.count k (θq p)) =
      twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) (Quotient.mk _ x) p *
        φ p := by
    intro p
    induction p using Quotient.inductionOn with
    | h y =>
      have h1 : θq (Quotient.mk _ y) = Quotient.mk _ (θ y) := rfl
      have h2 := quotientAverage_count_star_eq Γ θ θ.continuous f x y
      rw [h1, show (k : G → ℂ) = fun b => star (f (x⁻¹ * b)) from rfl, h2,
        twistedQuotientKernel_mk]
      simp only [RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply]
      ring
  rw [ha, hb]
  refine integral_congr_ae ?_
  filter_upwards [hd] with p hp
  rw [hp, hpt]

/-- **`R(f) ∘ I_θ` is the integral operator with kernel `K`.** For every `φ ∈ L²(Γ \ G, ν)`,
`(R(f) I_θ φ)(q) = ∫ K(q, q') φ(q') dν(q')` for `ν`-almost every `q`. -/
theorem twistedKernelOperator_ae_eq (μG : Measure G) [μG.IsHaarMeasure]
    (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : G ≃ₜ* G) (hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ)
    (hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν)
    (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
    (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG)
    (hπ : ∀ (g : G) (φ : Lp ℂ 2 ν),
      (π g φ : LeftQuotient Γ → ℂ) =ᵐ[ν] fun q => φ (rightTranslate Γ g q))
    (f : C_c(G, ℂ)) (φ : Lp ℂ 2 ν) :
    (((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν)) φ : LeftQuotient Γ → ℂ) =ᵐ[ν]
      fun q => ∫ q', twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) q q' *
        φ q' ∂ν := by
  have hq := leftQuotient_isOpenQuotientMap Γ
  have : ν.Regular := hν.regular
  have : LocallyCompactSpace (LeftQuotient Γ) := leftQuotient_locallyCompactSpace Γ
  have : SecondCountableTopology (LeftQuotient Γ) :=
    TopologicalSpace.Quotient.secondCountableTopology hq.isOpenMap
  have hact : Continuous (fun p : LeftQuotient Γ × G => rightTranslate Γ p.2 p.1) := by
    have hpq : IsOpenQuotientMap (Prod.map (leftQuotientMap Γ) (id : G → G)) :=
      hq.prodMap IsOpenQuotientMap.id
    rw [hpq.isQuotientMap.continuous_iff]
    exact hq.continuous.comp (continuous_fst.mul continuous_snd)
  have hpt := Langlands.Analysis.integratedTranslationPointwise (LeftQuotient Γ) ν G μG
    (fun q a => rightTranslate Γ a q) hact.measurable (fun g => hν.right_invariant g)
    π hπnorm hπmeas hπ f (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
  have heval : ∀ q : LeftQuotient Γ,
      ∫ a, f a * (twistOperator Γ θ hθΓ ν hθν φ : LeftQuotient Γ → ℂ) (rightTranslate Γ a q) ∂μG =
        ∫ q', twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) q q' * φ q' ∂ν := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => exact integral_mul_twistOperator_eq μG Γ ν hν θ hθΓ hθν f x φ
  filter_upwards [(hpt (twistOperator Γ θ hθΓ ν hθν φ)).2] with q hq'
  rw [ContinuousLinearMap.comp_apply, hq', heval]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- **The rows of the kernel are in `Lᵖ`.** Each row `q' ↦ K(q, q')` is continuous and vanishes off
a compact set, so it is in `Lᵖ(ν)` for a measure `ν` finite on compact sets. -/
theorem memLp_twistedQuotientKernel_row (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) [IsFiniteMeasureOnCompacts ν]
    (θ : G ≃ₜ* G) (hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ) (f : C_c(G, ℂ)) (q : LeftQuotient Γ)
    (p : ℝ≥0∞) :
    MemLp (twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) q) p ν := by
  have hq := leftQuotient_isOpenQuotientMap Γ
  have : T2Space (LeftQuotient Γ) := leftQuotient_t2Space Γ Subgroup.isClosed_of_discreteTopology
  have hK := continuous_uncurry_twistedQuotientKernel Γ θ θ.continuous
    (fun γ hγ => (hθΓ γ).2 hγ) f
  induction q using Quotient.inductionOn with
  | h x =>
    have hrow : Continuous (twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ)
        (Quotient.mk _ x)) :=
      hK.comp (continuous_const.prodMk continuous_id :
        Continuous fun q' : LeftQuotient Γ => ((Quotient.mk _ x : LeftQuotient Γ), q'))
    have hKc : IsCompact (leftQuotientMap Γ '' (θ.symm '' ((fun c => x * c) '' tsupport f))) :=
      ((f.hasCompactSupport.image (continuous_const.mul continuous_id :
        Continuous fun c : G => x * c)).image θ.symm.continuous).image hq.continuous
    refine Continuous.memLp_of_hasCompactSupport hrow (HasCompactSupport.intro hKc fun q' hq' => ?_)
    exact twistedQuotientKernel_mk_eq_zero Γ θ hθΓ f x q' hq'

/-- **The kernel is in `L²(ν × ν)` when `R(f) ∘ I_θ` is Hilbert–Schmidt.** -/
theorem memLp_uncurry_twistedQuotientKernel_of_isHilbertSchmidt (μG : Measure G)
    [μG.IsHaarMeasure] (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : G ≃ₜ* G) (hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ)
    (hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν)
    (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
    (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG)
    (hπ : ∀ (g : G) (φ : Lp ℂ 2 ν),
      (π g φ : LeftQuotient Γ → ℂ) =ᵐ[ν] fun q => φ (rightTranslate Γ g q))
    (f : C_c(G, ℂ))
    (hhs : IsHilbertSchmidt ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν))) :
    MemLp (Function.uncurry (twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ)))
      2 (ν.prod ν) := by
  have hq := leftQuotient_isOpenQuotientMap Γ
  have : ν.Regular := hν.regular
  have : LocallyCompactSpace (LeftQuotient Γ) := leftQuotient_locallyCompactSpace Γ
  have : SecondCountableTopology (LeftQuotient Γ) :=
    TopologicalSpace.Quotient.secondCountableTopology hq.isOpenMap
  exact memLp_uncurry_of_isHilbertSchmidt _ hhs _
    (continuous_uncurry_twistedQuotientKernel Γ θ θ.continuous
      (fun γ hγ => (hθΓ γ).2 hγ) f).aestronglyMeasurable
    (ae_of_all _ fun q => memLp_twistedQuotientKernel_row Γ ν θ hθΓ f q 2)
    (twistedKernelOperator_ae_eq μG Γ ν hν θ hθΓ hθν π hπnorm hπmeas hπ f)

/-- **The kernel is in `L²(ν × ν)` when `R(f) ∘ I_θ` is trace class.** -/
theorem memLp_uncurry_twistedQuotientKernel (μG : Measure G)
    [μG.IsHaarMeasure] (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : G ≃ₜ* G) (hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ)
    (hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν)
    (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
    (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG)
    (hπ : ∀ (g : G) (φ : Lp ℂ 2 ν),
      (π g φ : LeftQuotient Γ → ℂ) =ᵐ[ν] fun q => φ (rightTranslate Γ g q))
    (f : C_c(G, ℂ))
    (htc : IsTraceClass ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν))) :
    MemLp (Function.uncurry (twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ)))
      2 (ν.prod ν) :=
  memLp_uncurry_twistedQuotientKernel_of_isHilbertSchmidt μG Γ ν hν θ hθΓ hθν π hπnorm hπmeas hπ f
    (traceClassHilbertSchmidt _ _ htc)

end Analysis

end Langlands.TraceFormula
