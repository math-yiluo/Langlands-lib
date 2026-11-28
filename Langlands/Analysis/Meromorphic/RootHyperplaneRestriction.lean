import Langlands.Analysis.Meromorphic.RootHyperplanePoles
import Langlands.Analysis.Meromorphic.IdentityTheorem

/-! # Restriction of functions with root-hyperplane poles to a subspace

A scalar function `f` on a finite-dimensional complex vector space `X`, meromorphic in linear
coordinates with domain `D` and with poles along the hyperplanes of linear forms `L β`,
`β ∈ R` (`HasRootHyperplanePoles`), need not have any meaningful values on a linear subspace:
the domain `D` may miss the subspace entirely. This module shows that the composite with a
complex linear map `τ : V → X` is nevertheless meromorphic, with poles along the hyperplanes of
the pulled-back forms `L β ∘ τ`, as soon as none of these pulled-back forms vanishes, after `f` is
replaced off `D` by its regularization.

* `regularization F U` (on a normed space `E`) is `F` on `U` and, at a point `s` with clearing
  data `q · F = h` on `W ∩ U` (`IsClearingData`) and `q s ≠ 0`, the value `h s / q s`; these
  values do not depend on the data (`regularization_eq_div`). It is complex differentiable on
  `regularDomain F U` (`differentiableOn_regularization`), and every clearing data clear it on
  the whole of `W ∩ regularDomain F U` (`IsClearingData.mul_regularization`).
* `exists_comp_linearMap_of_hasRootHyperplanePoles`: for `f` meromorphic in coordinates with
  domain `D` and poles along the hyperplanes of `L β`, `β ∈ R`, and a complex linear map
  `τ : V → X` of finite-dimensional spaces with `L β ∘ τ ≠ 0` for every `β ∈ R`, there are a
  function `f'` on `V` and a domain `D'` such that `f'` is meromorphic in coordinates with domain
  `D'`, has poles along the hyperplanes of `L β ∘ τ`, `β ∈ R`, and `f' v = f (τ v)` whenever
  `τ v ∈ D`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set Filter Topology Metric
open scoped Manifold

section Regularization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Clearing data for `F` on `U`: an open set `W` and functions `q`, `h` complex differentiable
on `W` with `q s * F s = h s` for `s ∈ W ∩ U`. -/
def IsClearingData (F : E → ℂ) (U W : Set E) (q h : E → ℂ) : Prop :=
  IsOpen W ∧ DifferentiableOn ℂ q W ∧ DifferentiableOn ℂ h W ∧ ∀ s ∈ W ∩ U, q s * F s = h s

/-- The points of `U` together with the points `s` admitting clearing data `(W, q, h)` with
`s ∈ W` and `q s ≠ 0`. -/
def regularDomain (F : E → ℂ) (U : Set E) : Set E :=
  U ∪ {s | ∃ d : Set E × (E → ℂ) × (E → ℂ), IsClearingData F U d.1 d.2.1 d.2.2 ∧ s ∈ d.1 ∧
    d.2.1 s ≠ 0}

open Classical in
/-- The regularization of `F` on `U`: the value `F s` for `s ∈ U`, and `h s / q s` for chosen
clearing data `(W, q, h)` with `s ∈ W` and `q s ≠ 0` otherwise (`0` if there are none). -/
def regularization (F : E → ℂ) (U : Set E) (s : E) : ℂ :=
  if s ∈ U then F s else
    if hs : ∃ d : Set E × (E → ℂ) × (E → ℂ), IsClearingData F U d.1 d.2.1 d.2.2 ∧ s ∈ d.1 ∧
        d.2.1 s ≠ 0 then
      hs.choose.2.2 s / hs.choose.2.1 s
    else 0

variable {F : E → ℂ} {U : Set E}

theorem regularization_of_mem {s : E} (hs : s ∈ U) : regularization F U s = F s := by
  simp [regularization, hs]

theorem IsClearingData.isOpen_inter_ne_zero {W : Set E} {q h : E → ℂ}
    (hd : IsClearingData F U W q h) : IsOpen (W ∩ q ⁻¹' {0}ᶜ) :=
  hd.2.1.continuousOn.isOpen_inter_preimage hd.1 isOpen_compl_singleton

theorem IsClearingData.subset_regularDomain {W : Set E} {q h : E → ℂ}
    (hd : IsClearingData F U W q h) : W ∩ q ⁻¹' {0}ᶜ ⊆ regularDomain F U :=
  fun _ hs => Or.inr ⟨(W, q, h), hd, hs.1, hs.2⟩

theorem IsClearingData.continuousOn_div {W : Set E} {q h : E → ℂ}
    (hd : IsClearingData F U W q h) : ContinuousOn (fun s => h s / q s) (W ∩ q ⁻¹' {0}ᶜ) :=
  (hd.2.2.1.continuousOn.mono inter_subset_left).div
    (hd.2.1.continuousOn.mono inter_subset_left) fun _ hs => hs.2

variable (hUo : IsOpen U) (hUd : Dense U)
include hUo hUd

omit hUo in
/-- Two clearing data give the same quotient wherever both denominators are nonzero. -/
theorem IsClearingData.div_eq {W W' : Set E} {q h q' h' : E → ℂ}
    (hd : IsClearingData F U W q h) (hd' : IsClearingData F U W' q' h') {s : E}
    (hs : s ∈ W ∩ q ⁻¹' {0}ᶜ) (hs' : s ∈ W' ∩ q' ⁻¹' {0}ᶜ) :
    h s / q s = h' s / q' s := by
  set Ω := (W ∩ q ⁻¹' {0}ᶜ) ∩ (W' ∩ q' ⁻¹' {0}ᶜ)
  have hΩ : IsOpen Ω := hd.isOpen_inter_ne_zero.inter hd'.isOpen_inter_ne_zero
  have heq : EqOn (fun s => h s / q s) (fun s => h' s / q' s) (Ω ∩ U) := by
    intro x hx
    have h1 : q x * F x = h x := hd.2.2.2 x ⟨hx.1.1.1, hx.2⟩
    have h2 : q' x * F x = h' x := hd'.2.2.2 x ⟨hx.1.2.1, hx.2⟩
    have hq : q x ≠ 0 := hx.1.1.2
    have hq' : q' x ≠ 0 := hx.1.2.2
    simp only
    rw [← h1, ← h2, mul_div_cancel_left₀ _ hq, mul_div_cancel_left₀ _ hq']
  refine heq.of_subset_closure (hd.continuousOn_div.mono inter_subset_left)
    (hd'.continuousOn_div.mono inter_subset_right) inter_subset_left ?_ ⟨hs, hs'⟩
  intro x hx
  have := hΩ.inter_closure ⟨hx, hUd.closure_eq ▸ mem_univ x⟩
  exact this

omit hUo in
/-- At a point where the denominator of clearing data does not vanish, the regularization is
the quotient of the data. -/
theorem regularization_eq_div {W : Set E} {q h : E → ℂ} (hd : IsClearingData F U W q h)
    {s : E} (hsW : s ∈ W) (hq : q s ≠ 0) : regularization F U s = h s / q s := by
  by_cases hsU : s ∈ U
  · rw [regularization_of_mem hsU, ← hd.2.2.2 s ⟨hsW, hsU⟩, mul_div_cancel_left₀ _ hq]
  · have hex : ∃ d : Set E × (E → ℂ) × (E → ℂ), IsClearingData F U d.1 d.2.1 d.2.2 ∧
        s ∈ d.1 ∧ d.2.1 s ≠ 0 := ⟨(W, q, h), hd, hsW, hq⟩
    have hval : regularization F U s = hex.choose.2.2 s / hex.choose.2.1 s := by
      unfold regularization
      simp only [hsU, hex, ↓reduceIte, ↓reduceDIte]
    rw [hval]
    obtain ⟨hd', hs', hq'⟩ := hex.choose_spec
    exact hd'.div_eq hUd hd ⟨hs', hq'⟩ ⟨hsW, hq⟩

omit hUd in
theorem isOpen_regularDomain : IsOpen (regularDomain F U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro s (hs | ⟨d, hd, hsW, hq⟩)
  · exact ⟨U, subset_union_left, hUo, hs⟩
  · exact ⟨_, hd.subset_regularDomain, hd.isOpen_inter_ne_zero, hsW, hq⟩

/-- The regularization is complex differentiable on the regular domain, provided `F` is
complex differentiable on `U`. -/
theorem differentiableOn_regularization (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (regularization F U) (regularDomain F U) := by
  rintro s (hs | ⟨⟨W, q, h⟩, hd, hsW, hq⟩)
  · refine (((hF s hs).differentiableAt (hUo.mem_nhds hs)).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hUo.mem_nhds hs] with x hx
    exact regularization_of_mem hx
  · have hO := hd.isOpen_inter_ne_zero
    have hmem : s ∈ W ∩ q ⁻¹' {0}ᶜ := ⟨hsW, hq⟩
    have hdiv : DifferentiableOn ℂ (fun x => h x / q x) (W ∩ q ⁻¹' {0}ᶜ) := by
      simp_rw [div_eq_mul_inv]
      exact (hd.2.2.1.mono inter_subset_left).mul
        ((hd.2.1.mono inter_subset_left).fun_inv fun _ hx => hx.2)
    refine ((hdiv s hmem).differentiableAt (hO.mem_nhds hmem)).congr_of_eventuallyEq ?_
      |>.differentiableWithinAt
    filter_upwards [hO.mem_nhds hmem] with x hx
    exact regularization_eq_div hUd hd hx.1 hx.2

/-- Clearing data clear the regularization on the whole regular part of their open set. -/
theorem IsClearingData.mul_regularization (hF : DifferentiableOn ℂ F U) {W : Set E}
    {q h : E → ℂ} (hd : IsClearingData F U W q h) :
    ∀ s ∈ W ∩ regularDomain F U, q s * regularization F U s = h s := by
  have hO : IsOpen (W ∩ regularDomain F U) := hd.1.inter (isOpen_regularDomain hUo)
  have heq : EqOn (fun s => q s * regularization F U s) h (W ∩ U) := fun s hs => by
    simp only
    rw [regularization_of_mem hs.2]
    exact hd.2.2.2 s hs
  refine heq.of_subset_closure ?_ (hd.2.2.1.continuousOn.mono inter_subset_left) ?_ ?_
  · exact (hd.2.1.continuousOn.mono inter_subset_left).mul
      ((differentiableOn_regularization hUo hUd hF).continuousOn.mono inter_subset_right)
  · exact fun s hs => ⟨hs.1, subset_union_left hs.2⟩
  · intro s hs
    have := hO.inter_closure ⟨hs, hUd.closure_eq ▸ mem_univ s⟩
    refine closure_mono ?_ this
    exact fun x hx => ⟨hx.1.1, hx.2⟩

end Regularization

section NonVanishing

variable {n : ℕ} {κ : Type*}

/-- An affine form `t ↦ ψ (t - t₀)` on `ℂⁿ` is complex differentiable. -/
theorem differentiable_linearMap_sub (ψ : (Fin n → ℂ) →ₗ[ℂ] ℂ) (t₀ : Fin n → ℂ) :
    Differentiable ℂ (fun t => ψ (t - t₀)) := by
  have h : (fun t => ψ (t - t₀)) = fun t => LinearMap.toContinuousLinearMap ψ t - ψ t₀ := by
    funext t
    simp [map_sub]
  rw [h]
  exact (ContinuousLinearMap.differentiable _).sub_const _

/-- An affine form `t ↦ ψ (t - t₀)` with nonzero linear part does not vanish identically on any
ball around `t₀`. -/
theorem exists_mem_ball_linearMap_ne_zero {ψ : (Fin n → ℂ) →ₗ[ℂ] ℂ} (hψ : ψ ≠ 0)
    (t₀ : Fin n → ℂ) {r : ℝ} (hr : 0 < r) : ∃ t ∈ ball t₀ r, ψ (t - t₀) ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hψ (LinearMap.ext hcon)
  set c : ℝ := r / (2 * (‖v‖ + 1))
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  have hc : 0 < c := by positivity
  refine ⟨t₀ + (c : ℂ) • v, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hc.le]
    have hlt : c * ‖v‖ < c * (‖v‖ + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hc
    have hcv : c * (‖v‖ + 1) = r / 2 := by
      simp only [c]
      field_simp
    linarith
  · rw [add_sub_cancel_left, map_smul, smul_eq_mul]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') hv

/-- A finite product of affine forms `t ↦ φ β (t - t₀)` with nonzero linear parts does not
vanish identically on any ball around `t₀`. -/
theorem exists_mem_ball_prod_ne_zero (φ : κ → (Fin n → ℂ) →ₗ[ℂ] ℂ) (t₀ : Fin n → ℂ) {r : ℝ}
    (hr : 0 < r) (S : Finset κ) (hφ : ∀ β ∈ S, φ β ≠ 0) :
    ∃ t ∈ ball t₀ r, ∏ β ∈ S, φ β (t - t₀) ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨t₀, mem_ball_self hr, by simp⟩
  | insert β S hβ ih =>
    have hS := ih fun γ hγ => hφ γ (Finset.mem_insert_of_mem hγ)
    have hβ0 := exists_mem_ball_linearMap_ne_zero (hφ β (Finset.mem_insert_self β S)) t₀ hr
    have hball : IsPreconnected (ball t₀ r) := (convex_ball t₀ r).isPreconnected
    have hprod : Differentiable ℂ (fun t => ∏ γ ∈ S, φ γ (t - t₀)) :=
      differentiable_finsetProd_apply S fun γ _ => differentiable_linearMap_sub (φ γ) t₀
    obtain ⟨t, ht, hne⟩ := exists_mul_ne_zero_of_isOpen_subset
      (differentiable_linearMap_sub (φ β) t₀).differentiableOn isOpen_ball hball hβ0
      hprod.differentiableOn isOpen_ball hball hS isOpen_ball subset_rfl subset_rfl
      ⟨t₀, mem_ball_self hr⟩
    exact ⟨t, ht, by rwa [Finset.prod_insert hβ]⟩

end NonVanishing

section Restriction

variable {X V : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] {ι : Type*}

/-- **Restriction to a subspace.** Let `f` be meromorphic in linear coordinates on `X` with
domain `D` and with poles along the hyperplanes of the forms `L β`, `β ∈ R`, and let
`τ : V → X` be a complex linear map from a finite-dimensional space with `L β ∘ τ ≠ 0` for every
`β ∈ R`. Then some `f'` on `V`, meromorphic in linear coordinates with some domain `D'` and with
poles along the hyperplanes of the forms `L β ∘ τ`, `β ∈ R`, agrees with `f ∘ τ` at every `v`
with `τ v ∈ D`. The function `f'` is the composite with `τ` of the regularization of `f` in one
linear coordinate system. -/
theorem exists_comp_linearMap_of_hasRootHyperplanePoles [FiniteDimensional ℂ V]
    {L : ι → X →ₗ[ℂ] ℂ} {R : Set ι} {f : X → ℂ} {D : Set X}
    (hf : IsMeromorphicInCoordinatesOn f D) (hp : HasRootHyperplanePoles L R f D)
    (τ : V →ₗ[ℂ] X) (hτ : ∀ β ∈ R, L β ∘ₗ τ ≠ 0) :
    ∃ (f' : V → ℂ) (D' : Set V), IsMeromorphicInCoordinatesOn f' D' ∧
      HasRootHyperplanePoles (fun β => L β ∘ₗ τ) R f' D' ∧
      ∀ v, τ v ∈ D → f' v = f (τ v) := by
  classical
  have : FiniteDimensional ℂ X := hf.1
  set N := Module.finrank ℂ X
  let e₀ : (Fin N → ℂ) ≃ₗ[ℂ] X := (Module.finBasis ℂ X).equivFun.symm
  set U : Set (Fin N → ℂ) := e₀ ⁻¹' D with hUdef
  set F : (Fin N → ℂ) → ℂ := f ∘ e₀ with hFdef
  obtain ⟨hUo, hUd, hFhol, -⟩ := isMeromorphicOn_iff.mp (hf.2 N e₀)
  -- clearing data from the pole data in the coordinates `e₀`
  have hdata : ∀ s₀ : Fin N → ℂ, ∃ (S : Finset ι) (m : ℕ) (W : Set (Fin N → ℂ))
      (h : (Fin N → ℂ) → ℂ), (S : Set ι) ⊆ R ∧ s₀ ∈ W ∧
      IsClearingData F U W (fun s => (∏ β ∈ S, L β (e₀ s - e₀ s₀)) ^ m) h := by
    intro s₀
    obtain ⟨S, m, W, hSR, hWo, hs₀, h, hh, hEq⟩ := hp N e₀ s₀
    exact ⟨S, m, W, h, hSR, hs₀, hWo,
      ((differentiable_prod_linearForm_sub S L e₀ s₀).pow m).differentiableOn, hh,
      fun s hs => (hEq s hs.1 hs.2).symm⟩
  set Freg := regularization F U with hFregdef
  set O := regularDomain F U with hOdef
  have hOo : IsOpen O := isOpen_regularDomain hUo
  have hFreg : DifferentiableOn ℂ Freg O := differentiableOn_regularization hUo hUd hFhol
  let freg : X → ℂ := Freg ∘ e₀.symm
  let Dreg : Set X := e₀.symm ⁻¹' O
  have hfreg_eq : ∀ x ∈ D, freg x = f x := by
    intro x hx
    have hxU : e₀.symm x ∈ U := by simpa [U] using hx
    simp only [freg, Function.comp_apply]
    rw [hFregdef, regularization_of_mem hxU]
    simp [F]
  have hcoord : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X),
      DifferentiableOn ℂ (freg ∘ e) (e ⁻¹' Dreg) := by
    intro n e
    let T : (Fin n → ℂ) →L[ℂ] (Fin N → ℂ) :=
      LinearMap.toContinuousLinearMap (e₀.symm.toLinearMap ∘ₗ e.toLinearMap)
    have hT : freg ∘ e = Freg ∘ T := by
      funext s
      simp [freg, T]
    rw [hT]
    exact hFreg.comp T.differentiable.differentiableOn fun s hs => by simpa [T, Dreg] using hs
  have hDsub : D ⊆ Dreg := fun x hx => Or.inl (by simpa [U] using hx)
  have hpreg : HasRootHyperplanePoles L R freg Dreg := by
    refine hp.of_eqOn_dense hDsub (fun n e => ?_) (fun n e => (hcoord n e).continuousOn)
      fun x hx => (hfreg_eq x hx).symm
    rw [(hf.2 n e).2.1.closure_eq]
    exact subset_univ _
  refine ⟨freg ∘ τ, τ ⁻¹' Dreg, ?_, hpreg.comp_linearMap τ, fun v hv => hfreg_eq _ hv⟩
  -- meromorphy in one linear coordinate system of `V`
  set n := Module.finrank ℂ V
  let e' : (Fin n → ℂ) ≃ₗ[ℂ] V := (Module.finBasis ℂ V).equivFun.symm
  let A : (Fin n → ℂ) →L[ℂ] (Fin N → ℂ) :=
    LinearMap.toContinuousLinearMap (e₀.symm.toLinearMap ∘ₗ τ ∘ₗ e'.toLinearMap)
  have hA : ∀ t, e₀ (A t) = τ (e' t) := fun t => by simp [A]
  have hcomp : (freg ∘ τ) ∘ e' = Freg ∘ A := by
    funext t
    simp [freg, A]
  have hpre : e' ⁻¹' (τ ⁻¹' Dreg) = A ⁻¹' O := by
    ext t
    simp [Dreg, A]
  -- the pulled-back forms
  let φ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ := fun β => L β ∘ₗ τ ∘ₗ e'.toLinearMap
  have hφ : ∀ β ∈ R, φ β ≠ 0 := by
    intro β hβ h0
    apply hτ β hβ
    ext v
    have := LinearMap.congr_fun h0 (e'.symm v)
    simpa [φ] using this
  have hprodA : ∀ (S : Finset ι) (m : ℕ) (t₀ t : Fin n → ℂ),
      (∏ β ∈ S, L β (e₀ (A t) - e₀ (A t₀))) ^ m = (∏ β ∈ S, φ β (t - t₀)) ^ m := by
    intro S m t₀ t
    congr 1
    refine Finset.prod_congr rfl fun β _ => ?_
    simp only [hA, φ, LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub]
  -- local data at a point of `ℂⁿ`
  have hlocal : ∀ t₀ : Fin n → ℂ, ∃ (r : ℝ) (S : Finset ι) (m : ℕ) (W : Set (Fin N → ℂ))
      (h : (Fin N → ℂ) → ℂ), 0 < r ∧ (S : Set ι) ⊆ R ∧ ball t₀ r ⊆ A ⁻¹' W ∧
      IsClearingData F U W (fun s => (∏ β ∈ S, L β (e₀ s - e₀ (A t₀))) ^ m) h := by
    intro t₀
    obtain ⟨S, m, W, h, hSR, hsW, hd⟩ := hdata (A t₀)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hd.1.preimage A.continuous) t₀ hsW
    exact ⟨r, S, m, W, h, hr, hSR, hball, hd⟩
  have hne : ∀ (t₀ : Fin n → ℂ) (r : ℝ) (S : Finset ι) (m : ℕ), 0 < r → (S : Set ι) ⊆ R →
      ∃ t ∈ ball t₀ r, (∏ β ∈ S, φ β (t - t₀)) ^ m ≠ 0 := by
    intro t₀ r S m hr hSR
    obtain ⟨t, ht, h0⟩ := exists_mem_ball_prod_ne_zero φ t₀ hr S fun β hβ => hφ β (hSR hβ)
    exact ⟨t, ht, pow_ne_zero m h0⟩
  have hgdiff : ∀ (t₀ : Fin n → ℂ) (S : Finset ι) (m : ℕ),
      Differentiable ℂ (fun t => (∏ β ∈ S, φ β (t - t₀)) ^ m) := fun t₀ S m =>
    (differentiable_finsetProd_apply S fun β _ => differentiable_linearMap_sub (φ β) t₀).pow m
  apply isMeromorphicInCoordinatesOn_of_coordinates e'
  rw [hcomp, hpre, isMeromorphicOn_iff]
  refine ⟨hOo.preimage A.continuous, fun t₀ => ?_,
    hFreg.comp A.differentiable.differentiableOn (mapsTo_preimage A O), fun t₀ => ?_⟩
  · obtain ⟨r, S, m, W, h, hr, hSR, hball, hd⟩ := hlocal t₀
    have hsub := subset_closure_inter_ne_zero (hgdiff t₀ S m).differentiableOn isOpen_ball
      (convex_ball t₀ r).isPreconnected (hne t₀ r S m hr hSR) isOpen_ball subset_rfl
    refine closure_mono ?_ (hsub (mem_ball_self hr))
    rintro t ⟨htB, ht0⟩
    have hAt : A t ∈ W ∩ (fun s => (∏ β ∈ S, L β (e₀ s - e₀ (A t₀))) ^ m) ⁻¹' {0}ᶜ := by
      refine ⟨hball htB, ?_⟩
      simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
      rw [hprodA]
      exact ht0
    exact hd.subset_regularDomain hAt
  · obtain ⟨r, S, m, W, h, hr, hSR, hball, hd⟩ := hlocal t₀
    refine ⟨ball t₀ r, isOpen_ball, (convex_ball t₀ r).isConnected (nonempty_ball.mpr hr),
      mem_ball_self hr, fun t => (∏ β ∈ S, φ β (t - t₀)) ^ m, h ∘ A,
      (hgdiff t₀ S m).differentiableOn, hne t₀ r S m hr hSR,
      hd.2.2.1.comp A.differentiable.differentiableOn fun t ht => hball ht, ?_⟩
    rintro t ⟨htO, htB⟩
    have := hd.mul_regularization hUo hUd hFhol (A t) ⟨hball htB, htO⟩
    simp only [Function.comp_apply]
    rw [← hprodA]
    exact this

end Restriction

end Langlands.Analysis.Meromorphic
