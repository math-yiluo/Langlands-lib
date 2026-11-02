import Langlands.Global.Factors.FiniteComparisonStatement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

universe u

namespace Langlands.Global.FunctionalEquationComparison

variable {f g h : ℂ → ℂ}

lemma MeromorphicEq.refl (f : ℂ → ℂ) : MeromorphicEq f f :=
  fun _ => Filter.EventuallyEq.refl _ _

lemma MeromorphicEq.symm (hfg : MeromorphicEq f g) : MeromorphicEq g f :=
  fun z => (hfg z).symm

lemma MeromorphicEq.trans (hfg : MeromorphicEq f g) (hgh : MeromorphicEq g h) :
    MeromorphicEq f h := fun z => (hfg z).trans (hgh z)

lemma reflection_tendsto (z : ℂ) :
    Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] z) (𝓝[≠] (1 - z)) := by
  apply tendsto_inf.2
  constructor
  · exact ((continuous_const.sub continuous_id).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  · apply tendsto_principal.mpr
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_right_inj] using hs

lemma MeromorphicEq.reflect (hfg : MeromorphicEq f g) :
    MeromorphicEq (fun s => f (1 - s)) (fun s => g (1 - s)) :=
  fun z => (hfg (1 - z)).comp_tendsto (reflection_tendsto z)

lemma MeromorphicEq.finset_prod {Place : Type u} (S : Finset Place)
    {F G : Place → ℂ → ℂ} (hFG : ∀ v ∈ S, MeromorphicEq (F v) (G v)) :
    MeromorphicEq (fun s => ∏ v ∈ S, F v s) (fun s => ∏ v ∈ S, G v s) := by
  intro z
  filter_upwards [(eventually_all_finset S).2 (fun v hv => hFG v hv z)] with s hs
  exact Finset.prod_congr rfl hs

lemma NonzeroMeromorphic.eventually_ne_zero (hf : NonzeroMeromorphic f) (z : ℂ) :
    ∀ᶠ s in 𝓝[≠] z, f s ≠ 0 :=
  (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf.1 z)).mp (hf.2 z)

lemma nonzeroMeromorphic_of_eventually (hf : Meromorphic f)
    (h0 : ∀ z : ℂ, ∀ᶠ s in 𝓝[≠] z, f s ≠ 0) : NonzeroMeromorphic f :=
  ⟨hf, fun z => (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf z)).mpr (h0 z)⟩

lemma NonzeroMeromorphic.reflect (hf : NonzeroMeromorphic f) :
    NonzeroMeromorphic (fun s => f (1 - s)) := by
  apply nonzeroMeromorphic_of_eventually
  · intro z
    exact (hf.1 (1 - z)).comp_analyticAt (by fun_prop)
  · intro z
    exact (reflection_tendsto z).eventually (hf.eventually_ne_zero (1 - z))

lemma local_gamma_nonzero (F : LocalFactors)
    (hL : NonzeroMeromorphic F.lFactor) (hD : NonzeroMeromorphic F.dualLFactor)
    (hE : NonzeroMeromorphic F.epsilonFactor) : NonzeroMeromorphic F.gamma := by
  apply nonzeroMeromorphic_of_eventually
  · intro z
    exact ((hE.1 z).mul (hD.reflect.1 z)).div (hL.1 z)
  · intro z
    filter_upwards [hL.eventually_ne_zero z, hD.reflect.eventually_ne_zero z,
      hE.eventually_ne_zero z] with s hsL hsD hsE
    exact div_ne_zero (mul_ne_zero hsE hsD) hsL

lemma eq_on_halfplane_meromorphicEq {σ : ℝ} (hf : Meromorphic f) (hg : Meromorphic g)
    (hfg : ∀ s : ℂ, σ < s.re → f s = g s) : MeromorphicEq f g := by
  let z₀ : ℂ := (σ : ℂ) + 1
  have hz₀ : σ < z₀.re := by simp [z₀]
  have hnhds : ∀ᶠ s : ℂ in 𝓝 z₀, σ < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀
  have hzero : meromorphicOrderAt (f - g) z₀ = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds] with s hs
    exact sub_eq_zero.mpr (hfg s hs)
  intro z
  have hz : meromorphicOrderAt (f - g) z = ⊤ :=
    (hf.sub hg).meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ z₀) (Set.mem_univ z) hzero
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hz] with s hs
  exact sub_eq_zero.mp hs

lemma eulerTailComparison : EulerTailComparisonStatement.{u} := by
  intro Place _ S D E σ hDL hDD hEL hED hD hE hmatch
  have hpoint : ∀ s : ℂ, σ < s.re →
      D.partialL s = E.partialL s ∧ D.partialDualL s = E.partialDualL s := by
    intro s hs
    have hd := hD s hs
    have he := hE s hs
    constructor
    · have hd' : HasProd
          (fun v : {v : Place // v ∉ S} => (E.localFactors v).lFactor s)
          (D.partialL s) :=
        hd.1.congr_fun (fun v => (hmatch v.val v.property s hs).1.symm)
      exact hd'.unique he.1
    · have hd' : HasProd
          (fun v : {v : Place // v ∉ S} => (E.localFactors v).dualLFactor s)
          (D.partialDualL s) :=
        hd.2.congr_fun (fun v => (hmatch v.val v.property s hs).2.symm)
      exact hd'.unique he.2
  exact ⟨eq_on_halfplane_meromorphicEq hDL hEL (fun s hs => (hpoint s hs).1),
    eq_on_halfplane_meromorphicEq hDD hED (fun s hs => (hpoint s hs).2)⟩


lemma MeromorphicEq.div {f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (hf : MeromorphicEq f₁ f₂) (hg : MeromorphicEq g₁ g₂) :
    MeromorphicEq (fun s => f₁ s / g₁ s) (fun s => f₂ s / g₂ s) := by
  intro z
  filter_upwards [hf z, hg z] with s hs ht
  rw [hs, ht]

lemma finiteGamma_formula {Place : Type u} (D : FiniteEulerData Place)
    (S : Finset Place) (s : ℂ) :
    D.finiteGamma S s = D.finiteEpsilon S s *
      (∏ v ∈ S, (D.localFactors v).dualLFactor (1 - s)) /
      (∏ v ∈ S, (D.localFactors v).lFactor s) := by
  simp only [FiniteEulerData.finiteGamma, LocalFactors.gamma,
    FiniteEulerData.finiteEpsilon, Finset.prod_div_distrib, Finset.prod_mul_distrib]

lemma finiteGamma_eq_tail_ratio {Place : Type u} (D : FiniteEulerData Place)
    (S : Finset Place) (hD : Admissible D S) (hFE : FunctionalEquation D S) :
    MeromorphicEq (D.finiteGamma S)
      (fun s => D.partialL s / D.partialDualL (1 - s)) := by
  intro z
  have hL : ∀ᶠ s in 𝓝[≠] z, ∀ v ∈ S, (D.localFactors v).lFactor s ≠ 0 :=
    (eventually_all_finset S).mpr
      (fun v hv => (hD.2.2 v hv).1.eventually_ne_zero z)
  filter_upwards [hFE z, hL, hD.2.1.reflect.eventually_ne_zero z] with s hsFE hsL hsT
  have hsP : (∏ v ∈ S, (D.localFactors v).lFactor s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hsL
  rw [finiteGamma_formula]
  apply (div_eq_div_iff hsP hsT).mpr
  change D.partialL s * (∏ v ∈ S, (D.localFactors v).lFactor s) =
    D.finiteEpsilon S s *
      (D.partialDualL (1 - s) * ∏ v ∈ S, (D.localFactors v).dualLFactor (1 - s))
      at hsFE
  calc
    (D.finiteEpsilon S s * (∏ v ∈ S, (D.localFactors v).dualLFactor (1 - s))) *
        D.partialDualL (1 - s) =
      D.finiteEpsilon S s *
        (D.partialDualL (1 - s) * ∏ v ∈ S, (D.localFactors v).dualLFactor (1 - s)) :=
      by ring
    _ = D.partialL s * (∏ v ∈ S, (D.localFactors v).lFactor s) := hsFE.symm

lemma finiteGammaComparison : FiniteGammaComparisonStatement.{u} := by
  intro Place S D E hD hE hDFE hEFE hL hDual
  exact (finiteGamma_eq_tail_ratio D S hD hDFE).trans
    ((hL.div hDual.reflect).trans (finiteGamma_eq_tail_ratio E S hE hEFE).symm)

lemma globalFiniteGammaComparison : GlobalFiniteGammaComparisonStatement.{u} := by
  intro Place _ S D E h
  obtain ⟨hD, hE, hDFE, hEFE, σ, hDp, hEp, hmatch⟩ := h
  obtain ⟨hL, hDual⟩ := eulerTailComparison Place S D E σ hD.1.1 hD.2.1.1
    hE.1.1 hE.2.1.1 hDp hEp hmatch
  exact finiteGammaComparison Place S D E hD hE hDFE hEFE hL hDual

lemma finiteBlockCancellation : FiniteBlockCancellationStatement.{u} := by
  intro Place _ S A F G hAS hnon hprod haux
  have hauxprod : MeromorphicEq (fun s => ∏ v ∈ S \ A, F v s)
      (fun s => ∏ v ∈ S \ A, G v s) :=
    MeromorphicEq.finset_prod (S \ A) (fun v hv =>
      haux v (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2)
  intro z
  have h0 : ∀ᶠ s in 𝓝[≠] z, ∀ v ∈ S \ A, F v s ≠ 0 :=
    (eventually_all_finset (S \ A)).mpr (fun v hv =>
      (hnon v (Finset.mem_sdiff.mp hv).1).1.eventually_ne_zero z)
  filter_upwards [hprod z, hauxprod z, h0] with s hsprod hsaux hs0
  have hp0 : (∏ v ∈ S \ A, F v s) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
  apply mul_left_cancel₀ hp0
  calc
    (∏ v ∈ S \ A, F v s) * (∏ v ∈ A, F v s) = ∏ v ∈ S, F v s :=
      Finset.prod_sdiff hAS
    _ = ∏ v ∈ S, G v s := hsprod
    _ = (∏ v ∈ S \ A, G v s) * (∏ v ∈ A, G v s) :=
      (Finset.prod_sdiff hAS).symm
    _ = (∏ v ∈ S \ A, F v s) * (∏ v ∈ A, G v s) := by rw [hsaux]


lemma admissible_gamma_nonzero {Place : Type u} {D : FiniteEulerData Place}
    {S : Finset Place} (hD : Admissible D S) (v : Place) (hv : v ∈ S) :
    NonzeroMeromorphic (D.localFactors v).gamma := by
  obtain ⟨hL, hDual, hE⟩ := hD.2.2 v hv
  exact local_gamma_nonzero (D.localFactors v) hL hDual hE

lemma twoTwistIsolation : TwoTwistIsolationStatement.{u} := by
  intro Place _ S A w F G D₁ E₁ D₂ E₂ hAS hwS hwA h₁ h₂
    hD₁A hE₁A hstable₁ hD₂A hE₂A hstable₂
  have hnon₁ : ∀ v ∈ S, NonzeroMeromorphic (D₁.localFactors v).gamma ∧
      NonzeroMeromorphic (E₁.localFactors v).gamma :=
    fun v hv => ⟨admissible_gamma_nonzero h₁.1 v hv,
      admissible_gamma_nonzero h₁.2.1 v hv⟩
  have harch₁ := finiteBlockCancellation Place S A
    (fun v => (D₁.localFactors v).gamma) (fun v => (E₁.localFactors v).gamma)
    hAS hnon₁ (globalFiniteGammaComparison Place S D₁ E₁ h₁)
    (fun v hv hnv => hstable₁ v (Finset.mem_sdiff.mpr ⟨hv, hnv⟩))
  have harch : MeromorphicEq (fun s => ∏ v ∈ A, (F v).gamma s)
      (fun s => ∏ v ∈ A, (G v).gamma s) :=
    (MeromorphicEq.finset_prod A hD₁A).symm.trans
      (harch₁.trans (MeromorphicEq.finset_prod A hE₁A))
  have hBS : insert w A ⊆ S := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hwS
    · exact hAS hv
  have hnon₂ : ∀ v ∈ S, NonzeroMeromorphic (D₂.localFactors v).gamma ∧
      NonzeroMeromorphic (E₂.localFactors v).gamma :=
    fun v hv => ⟨admissible_gamma_nonzero h₂.1 v hv,
      admissible_gamma_nonzero h₂.2.1 v hv⟩
  have hblock₂ := finiteBlockCancellation Place S (insert w A)
    (fun v => (D₂.localFactors v).gamma) (fun v => (E₂.localFactors v).gamma)
    hBS hnon₂ (globalFiniteGammaComparison Place S D₂ E₂ h₂)
    (fun v hv hnv => hstable₂ v (Finset.mem_sdiff.mpr ⟨hv, hnv⟩))
  have hblock : MeromorphicEq (fun s => ∏ v ∈ insert w A, (F v).gamma s)
      (fun s => ∏ v ∈ insert w A, (G v).gamma s) :=
    (MeromorphicEq.finset_prod (insert w A) hD₂A).symm.trans
      (hblock₂.trans (MeromorphicEq.finset_prod (insert w A) hE₂A))
  refine ⟨harch, ?_⟩
  intro z
  have h0 : ∀ᶠ s in 𝓝[≠] z, ∀ v ∈ A, (F v).gamma s ≠ 0 := by
    apply (eventually_all_finset A).mpr
    intro v hv
    filter_upwards [hD₂A v (Finset.mem_insert_of_mem hv) z,
      (hnon₂ v (hAS hv)).1.eventually_ne_zero z] with s hvs h0s
    rw [← hvs]
    exact h0s
  filter_upwards [harch z, hblock z, h0] with s hsarch hsblock hs0
  simp only [Finset.prod_insert hwA] at hsblock
  rw [← hsarch] at hsblock
  exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr hs0) hsblock

/-- The full conditional finite-exceptional-set comparison engine. -/
theorem finiteFunctionalEquationComparison :
    FiniteFunctionalEquationComparisonStatement.{u} :=
  ⟨eulerTailComparison, finiteGammaComparison, globalFiniteGammaComparison,
    finiteBlockCancellation, twoTwistIsolation⟩

end Langlands.Global.FunctionalEquationComparison
