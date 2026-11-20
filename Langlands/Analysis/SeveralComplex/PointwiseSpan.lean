import Langlands.Analysis.SeveralComplex.ZeroCounting
import Langlands.Analysis.SeveralComplex.RankWitness
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Local finiteness of pointwise spans of holomorphic families

Let `E` and `F` be finite-dimensional complex normed spaces, `U ⊆ E` open, and
`a : Λ → E → F` an arbitrary family of maps holomorphic on `U`. Then every point `x₀ ∈ U` has
an open neighbourhood `V ⊆ U` and a finite set `s ⊆ Λ` such that at every `z ∈ V` the span of
all vectors `a l z` is already spanned by the `a μ z` with `μ ∈ s`.

In particular (with `F = ℂ`) the common zero set of an arbitrary family of holomorphic functions
is, near every point, the common zero set of finitely many of them.

The proof is by induction on `finrank ℂ E`. Near `x₀`, `exists_det_witness` gives a holomorphic
determinant `h` and finitely many indices `s₁` such that at every point where `h` is nonzero
the members with indices in `s₁` span the full pointwise span of the family. (Only this
implication is used; the converse can fail.) If `h x₀ ≠ 0` we are done. Otherwise `h` is not
identically zero on the complex line through `x₀` and a point `z₁` with `h z₁ ≠ 0`, so it has
an isolated zero at `x₀` on that line. Splitting `E = ker ℓ ⊕ ℂ v` along that line, `exists_powerSum_family` produces a
holomorphic family `T` on a ball in `ker ℓ` (one dimension less), to which the induction
hypothesis applies, giving `s₀`; at every zero of `h` near `x₀` the members with indices in
`s₀` span. The finite set is `s₀ ∪ s₁`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter Module
open scoped Topology

universe u v w

/-- The **pointwise span** of a family `a : Λ → E → F` over a set `s` of indices at `z`: the
complex span of the vectors `a μ z`, `μ ∈ s`. -/
def pointwiseSpan {Λ : Type*} {E : Type*} {F : Type*} [AddCommGroup F] [Module ℂ F]
    (a : Λ → E → F) (s : Set Λ) (z : E) : Submodule ℂ F :=
  Submodule.span ℂ ((fun μ => a μ z) '' s)

/-- The induction behind `exists_finset_span_eq`, on `d = finrank ℂ E`. -/
theorem exists_finset_span_eq_aux {Λ : Type w} (d : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E],
    finrank ℂ E = d →
    ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
      (U : Set E), IsOpen U → ∀ (a : Λ → E → F), (∀ l, DifferentiableOn ℂ (a l) U) →
      ∀ x₀ ∈ U, ∃ V ⊆ U, IsOpen V ∧ x₀ ∈ V ∧ ∃ s : Finset Λ,
        ∀ z ∈ V, ∀ l, a l z ∈ Submodule.span ℂ ((fun μ => a μ z) '' (s : Set Λ)) := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro E _ _ _ hd F _ _ _ U hU a ha x₀ hx₀
  classical
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  obtain ⟨r, hr, hBU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set B := ball x₀ r with hBdef
  obtain ⟨z₁, hz₁, s₁, h, hh, hz₁h, hwit⟩ :=
    exists_det_witness (U := B) ⟨x₀, mem_ball_self hr⟩ fun l => (ha l).mono hBU
  by_cases hx₀h : h x₀ ≠ 0
  · -- the generic case: `s₁` works near `x₀`
    refine ⟨B ∩ h ⁻¹' {0}ᶜ, inter_subset_left.trans hBU,
      hh.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton,
      ⟨mem_ball_self hr, hx₀h⟩, s₁, fun z hz l => hwit z hz.1 hz.2 l⟩
  rw [not_not] at hx₀h
  -- the direction of a line through `x₀` on which `h` is not identically zero
  set v : E := z₁ - x₀ with hvdef
  have hv : v ≠ 0 := by
    intro h0
    rw [hvdef, sub_eq_zero] at h0
    exact hz₁h (h0 ▸ hx₀h)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set Ω : Set ℂ := ball (0 : ℂ) (r / ‖v‖) with hΩdef
  have hΩB : ∀ t ∈ Ω, x₀ + t • v ∈ B := by
    intro t ht
    rw [hΩdef, mem_ball, dist_zero_right, lt_div_iff₀ hvpos] at ht
    rw [hBdef, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  set g : ℂ → ℂ := fun t => h (x₀ + t • v) with hgdef
  have hg : DifferentiableOn ℂ g Ω :=
    hh.comp ((differentiableOn_const x₀).add (differentiableOn_id.smul_const v)) hΩB
  have h1Ω : (1 : ℂ) ∈ Ω := by
    rw [hΩdef, mem_ball, dist_zero_right, norm_one, one_lt_div hvpos, hvdef, ← dist_eq_norm]
    exact hz₁
  have h0Ω : (0 : ℂ) ∈ Ω := mem_ball_self (div_pos hr hvpos)
  have hgA : AnalyticOnNhd ℂ g Ω := hg.analyticOnNhd isOpen_ball
  -- `g` has an isolated zero at `0`
  have hiso : ∀ᶠ t in 𝓝[≠] (0 : ℂ), g t ≠ 0 := by
    rcases (hgA 0 h0Ω).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
    · exfalso
      have := hgA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball _ _).isPreconnected h0Ω h0 h1Ω
      apply hz₁h
      simpa [hgdef, hvdef] using this
    · exact h0
  obtain ⟨ε, hε, hεg⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hiso)
  set ρ : ℝ := min ε (r / ‖v‖) / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have := min_le_left ε (r / ‖v‖); rw [hρdef]; linarith
  have hρΩ : ρ < r / ‖v‖ := by
    have := min_le_right ε (r / ‖v‖)
    have : 0 < r / ‖v‖ := div_pos hr hvpos
    rw [hρdef]; linarith
  -- a complementary hyperplane
  obtain ⟨g₀, -, hg₀v⟩ := exists_dual_vector ℂ v hvpos.ne'
  set ℓ : E →L[ℂ] ℂ := ((‖v‖ : ℂ))⁻¹ • g₀ with hℓdef
  have hℓv : ℓ v = 1 := by
    have : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hvpos.ne'
    simp [hℓdef, hg₀v, this]
  set Pk : Submodule ℂ E := LinearMap.ker (ℓ : E →ₗ[ℂ] ℂ) with hPkdef
  have hPk : finrank ℂ Pk < d := by
    rw [← hd]
    refine Submodule.finrank_lt fun htop => ?_
    have : v ∈ Pk := htop ▸ Submodule.mem_top
    rw [hPkdef, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hℓv] at this
    exact one_ne_zero this
  -- coordinates `(w, t) ↦ x₀ + w + t • v`
  set Φ : Pk × ℂ → E := fun p => x₀ + Pk.subtypeL p.1 + p.2 • v with hΦdef
  have hΦd : Differentiable ℂ Φ :=
    ((differentiable_const x₀).add (Pk.subtypeL.differentiable.comp differentiable_fst)).add
      (differentiable_snd.smul_const v)
  set O : Set (Pk × ℂ) := Φ ⁻¹' B with hOdef
  have hO : IsOpen O := isOpen_ball.preimage hΦd.continuous
  have hHd : DifferentiableOn ℂ (h ∘ Φ) O := hh.comp hΦd.differentiableOn fun p hp => hp
  have hbd : ∀ l, DifferentiableOn ℂ (fun p => a l (Φ p)) O :=
    fun l => ((ha l).mono hBU).comp hΦd.differentiableOn fun p hp => hp
  have hΦ0 : ∀ t : ℂ, Φ (0, t) = x₀ + t • v := by
    intro t; simp [hΦdef]
  have hρO : ∀ t ∈ closedBall (0 : ℂ) ρ, ((0 : Pk), t) ∈ O := by
    intro t ht
    show Φ (0, t) ∈ B
    rw [hΦ0]
    refine hΩB t ?_
    rw [hΩdef, mem_ball]
    exact (mem_closedBall.1 ht).trans_lt hρΩ
  have hne : ∀ t ∈ sphere (0 : ℂ) ρ, (h ∘ Φ) (0, t) ≠ 0 := by
    intro t ht
    rw [Function.comp_apply, hΦ0]
    refine hεg (by rw [mem_sphere] at ht; rw [ht]; exact hρε) ?_
    intro h0
    rw [h0, mem_sphere, dist_self] at ht
    exact hρ.ne' ht.symm
  obtain ⟨k, δ, hδ, T, hT, htransfer⟩ :=
    exists_powerSum_family (Λ := Λ) hO hHd hbd hρ hρO hne
  -- the induction hypothesis on the hyperplane
  obtain ⟨V', hV'δ, hV'open, h0V', s₀, hs₀⟩ :=
    IH (finrank ℂ Pk) hPk Pk rfl (Fin k → F) (ball (0 : Pk) δ) isOpen_ball T hT 0
      (mem_ball_self hδ)
  -- coordinates of a point of `E`
  set π : E → Pk × ℂ := fun z =>
    (⟨(z - x₀) - ℓ (z - x₀) • v, by
      rw [hPkdef, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, map_smul, hℓv,
        smul_eq_mul, mul_one, sub_self]⟩, ℓ (z - x₀)) with hπdef
  have hπc : Continuous π := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
    · exact (continuous_id.sub continuous_const).sub
        ((ℓ.continuous.comp (continuous_id.sub continuous_const)).smul continuous_const)
    · exact ℓ.continuous.comp (continuous_id.sub continuous_const)
  have hΦπ : ∀ z, Φ (π z) = z := by
    intro z
    simp only [hΦdef, hπdef, Submodule.subtypeL_apply]
    abel
  have hπx₀ : π x₀ = (0, 0) := by
    simp only [hπdef, sub_self, map_zero, zero_smul, Prod.mk.injEq, and_true]
    rfl
  refine ⟨B ∩ π ⁻¹' (V' ×ˢ ball 0 ρ), inter_subset_left.trans hBU,
    isOpen_ball.inter ((hV'open.prod isOpen_ball).preimage hπc),
    ⟨mem_ball_self hr, by rw [mem_preimage, hπx₀]; exact ⟨h0V', mem_ball_self hρ⟩⟩,
    s₀ ∪ s₁, ?_⟩
  intro z hz l
  have hsub : ∀ s' : Finset Λ, s' ⊆ s₀ ∪ s₁ →
      Submodule.span ℂ ((fun μ => a μ z) '' (s' : Set Λ)) ≤
        Submodule.span ℂ ((fun μ => a μ z) '' ((s₀ ∪ s₁ : Finset Λ) : Set Λ)) :=
    fun s' hs' => Submodule.span_mono (image_mono (Finset.coe_subset.2 hs'))
  by_cases hhz : h z = 0
  · -- `z` is a zero of `h`: use the induction hypothesis
    obtain ⟨hzB, hzV', hzρ⟩ := hz
    have hw : (π z).1 ∈ ball (0 : Pk) δ := hV'δ hzV'
    have hH0 : (h ∘ Φ) ((π z).1, (π z).2) = 0 := by
      rw [Function.comp_apply, Prod.mk.eta, hΦπ]; exact hhz
    have := htransfer (π z).1 hw s₀ (hs₀ (π z).1 hzV') (π z).2 hzρ hH0 l
    simp only [Prod.mk.eta, hΦπ] at this
    exact hsub s₀ Finset.subset_union_left this
  · exact hsub s₁ Finset.subset_union_right (hwit z hz.1 hhz l)

/-- **Local finiteness of pointwise spans.** For a family `a : Λ → E → F` of maps holomorphic on
an open set `U` of a finite-dimensional complex normed space, with values in a
finite-dimensional complex normed space, every `x₀ ∈ U` has an open neighbourhood `V ⊆ U` and a
finite set `s` of indices such that for all `z ∈ V` and all `l`, `a l z` lies in the span of
`{a μ z | μ ∈ s}`. -/
theorem exists_finset_span_eq {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {Λ : Type w} {U : Set E} (hU : IsOpen U) {a : Λ → E → F}
    (ha : ∀ l, DifferentiableOn ℂ (a l) U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ V ⊆ U, IsOpen V ∧ x₀ ∈ V ∧ ∃ s : Finset Λ,
      ∀ z ∈ V, ∀ l, a l z ∈ Submodule.span ℂ ((fun μ => a μ z) '' (s : Set Λ)) :=
  exists_finset_span_eq_aux (finrank ℂ E) E rfl F U hU a ha x₀ hx₀

/-- **Local finiteness of pointwise spans**, as an equality of spans: near every point of `U`,
the pointwise span of the whole family equals the pointwise span over a finite set of
indices. -/
theorem exists_finset_pointwiseSpan_eq {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {Λ : Type w} {U : Set E} (hU : IsOpen U) {a : Λ → E → F}
    (ha : ∀ l, DifferentiableOn ℂ (a l) U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ V ⊆ U, IsOpen V ∧ x₀ ∈ V ∧ ∃ s : Finset Λ,
      ∀ z ∈ V, pointwiseSpan a univ z = pointwiseSpan a (s : Set Λ) z := by
  obtain ⟨V, hVU, hV, hx₀V, s, hs⟩ := exists_finset_span_eq hU ha hx₀
  refine ⟨V, hVU, hV, hx₀V, s, fun z hz => le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨l, -, rfl⟩
    exact hs z hz l
  · exact Submodule.span_mono (image_mono (subset_univ _))

/-- **Common zeros of a family of holomorphic functions are locally finitely defined.** For a
family `f : Λ → E → ℂ` of functions holomorphic on an open set `U` of a finite-dimensional
complex normed space, every `x₀ ∈ U` has an open neighbourhood `V ⊆ U` and a finite set `s` of
indices such that a point of `V` is a common zero of all `f l` as soon as it is a common zero of
the `f μ` with `μ ∈ s`. -/
theorem exists_finset_zero_iff {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {Λ : Type w} {U : Set E} (hU : IsOpen U) {f : Λ → E → ℂ}
    (hf : ∀ l, DifferentiableOn ℂ (f l) U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ V ⊆ U, IsOpen V ∧ x₀ ∈ V ∧ ∃ s : Finset Λ,
      ∀ z ∈ V, (∀ l, f l z = 0) ↔ ∀ μ ∈ s, f μ z = 0 := by
  obtain ⟨V, hVU, hV, hx₀V, s, hs⟩ := exists_finset_span_eq hU hf hx₀
  refine ⟨V, hVU, hV, hx₀V, s, fun z hz => ⟨fun h μ _ => h μ, fun h l => ?_⟩⟩
  have hspan : Submodule.span ℂ ((fun μ => f μ z) '' (s : Set Λ)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨μ, hμ, rfl⟩
    exact h μ hμ
  have := hs z hz l
  rwa [hspan, Submodule.mem_bot] at this

end Langlands.Analysis.SeveralComplex
