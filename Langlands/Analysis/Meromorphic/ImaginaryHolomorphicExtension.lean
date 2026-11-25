import Langlands.Analysis.Meromorphic.ScalarIdentity
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.Analysis.Meromorphic.ImaginaryHyperplaneDivision
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Holomorphy near the imaginary subspace from an isometry identity

Mœglin–Waldspurger IV.3.12 and Lapid 2011, pp.328–329, in coordinates: a finite expansion
`∑ i, coeff i s • ψ i` with meromorphic coefficients on `ℂⁿ`, whose singularities near every
imaginary point lie on hyperplanes with real normal vectors and whose Gram form is constant on
the imaginary points where it is holomorphic, has a representation with coefficients that are
holomorphic on a neighbourhood of `iℝⁿ`. -/

noncomputable section

open Set Filter Metric
open scoped Topology Manifold ComplexOrder

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

/-! ## Scalar meromorphic functions on a normed space

The lemmas of this section are private helper lemmas. -/

section Scalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : E → ℂ} {U V W : Set E}

/-- Multiplication by a constant keeps the domain of holomorphy. -/
private theorem IsMeromorphicOn.mul_const (hf : IsMeromorphicOn 𝓘(ℂ, E) f U) (c : ℂ) :
    IsMeromorphicOn 𝓘(ℂ, E) (fun x => f x * c) U := by
  have h := hf.mul (isMeromorphicOn_const (E := E) c)
  rw [inter_univ] at h
  exact h

end Scalar

end Langlands.Analysis.Meromorphic

namespace Langlands.Analysis.Meromorphic.ImaginaryHyperplane

open Langlands.Analysis.Meromorphic

/-! ## Maximal holomorphic extension of a meromorphic function on `ℂⁿ` -/

section Extension

variable {n : ℕ}

/-- The set of points near which `f` agrees on `D` with a holomorphic function. -/
def extensionDomain (f : (Fin n → ℂ) → ℂ) (D : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {s | ∃ N : Set (Fin n → ℂ), IsOpen N ∧ s ∈ N ∧ ∃ c : (Fin n → ℂ) → ℂ,
    DifferentiableOn ℂ c N ∧ EqOn c f (N ∩ D)}

/-- The extension of `f` by limits along `D`. -/
def maximalExtension (f : (Fin n → ℂ) → ℂ) (D : Set (Fin n → ℂ)) : (Fin n → ℂ) → ℂ :=
  fun s => limUnder (𝓝[D] s) f

variable {f : (Fin n → ℂ) → ℂ} {D : Set (Fin n → ℂ)}

theorem isOpen_extensionDomain : IsOpen (extensionDomain f D) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _s ⟨N, hN, hsN, c, hc, hcf⟩
  exact ⟨N, fun y hy => ⟨N, hN, hy, c, hc, hcf⟩, hN, hsN⟩

theorem maximalExtension_eqOn (hD : Dense D) {N : Set (Fin n → ℂ)} (hN : IsOpen N)
    {c : (Fin n → ℂ) → ℂ} (hc : DifferentiableOn ℂ c N) (hcf : EqOn c f (N ∩ D)) :
    EqOn (maximalExtension f D) c N := by
  intro s hs
  have : NeBot (𝓝[D] s) := mem_closure_iff_nhdsWithin_neBot.mp (hD.closure_eq ▸ mem_univ s)
  apply Tendsto.limUnder_eq
  have hcont : ContinuousAt c s := hc.continuousOn.continuousAt (hN.mem_nhds hs)
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [inter_mem_nhdsWithin D (hN.mem_nhds hs)] with y hy
  exact hcf ⟨hy.2, hy.1⟩

theorem subset_extensionDomain (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D) :
    D ⊆ extensionDomain f D := fun _ hs =>
  ⟨D, hf.1, hs, f, isHolomorphicOn_iff_differentiableOn_scalar.mp hf.2.2.1, fun _ _ => rfl⟩

theorem maximalExtension_eqOn_self (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D) :
    EqOn (maximalExtension f D) f D :=
  maximalExtension_eqOn hf.2.1 hf.1 (isHolomorphicOn_iff_differentiableOn_scalar.mp hf.2.2.1)
    fun _ _ => rfl

theorem differentiableOn_maximalExtension (hD : Dense D) :
    DifferentiableOn ℂ (maximalExtension f D) (extensionDomain f D) := by
  rintro s ⟨N, hN, hsN, c, hc, hcf⟩
  have heq : maximalExtension f D =ᶠ[𝓝 s] c :=
    Filter.eventually_of_mem (hN.mem_nhds hsN) (maximalExtension_eqOn hD hN hc hcf)
  exact ((hc.differentiableAt (hN.mem_nhds hsN)).congr_of_eventuallyEq heq).differentiableWithinAt

/-- The maximal extension is meromorphic with the extension domain as domain of holomorphy. -/
theorem isMeromorphicOn_maximalExtension (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (maximalExtension f D) (extensionDomain f D) := by
  have hsub := subset_extensionDomain hf
  have hdiff := differentiableOn_maximalExtension (f := f) hf.2.1
  refine ⟨isOpen_extensionDomain, hf.2.1.mono hsub,
    isHolomorphicOn_iff_differentiableOn_scalar.mpr hdiff, fun s₀ => ?_⟩
  obtain ⟨W, hW, hcW, hs₀W, g, h, hg, hgnz, hh, hgh⟩ := hf.2.2.2 s₀
  refine ⟨W, hW, hcW, hs₀W, g, h, hg, hgnz, hh, ?_⟩
  have hg' : DifferentiableOn ℂ g W := hg.differentiableOn
  have hh' : DifferentiableOn ℂ h W := isHolomorphicOn_iff_differentiableOn_scalar.mp hh
  have hopen : IsOpen (extensionDomain f D ∩ W) := isOpen_extensionDomain.inter hW
  have heq : EqOn (fun s => g s • maximalExtension f D s) h
      ((extensionDomain f D ∩ W) ∩ D) := by
    rintro s ⟨⟨-, hsW⟩, hsD⟩
    simp only
    rw [maximalExtension_eqOn_self hf hsD]
    exact hgh s ⟨hsD, hsW⟩
  have := heq.of_subset_closure
    ((hg'.continuousOn.mono inter_subset_right).smul (hdiff.continuousOn.mono inter_subset_left))
    (hh'.continuousOn.mono inter_subset_right) inter_subset_left
    (hf.2.1.open_subset_closure_inter hopen)
  intro s hs
  exact this ⟨hs.1, hs.2⟩

end Extension

/-! ## Transport along linear isomorphisms and charts -/

section Transport

/-- Meromorphy on a normed space is preserved by composition with a continuous linear
isomorphism. -/
theorem isMeromorphicOn_comp_continuousLinearEquiv {E E' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] {f : E → ℂ} {U : Set E}
    (hf : IsMeromorphicOn 𝓘(ℂ, E) f U) (T : E' ≃L[ℂ] E) :
    IsMeromorphicOn 𝓘(ℂ, E') (f ∘ T) (T ⁻¹' U) := by
  obtain ⟨hU, hUd, hhol, hloc⟩ := hf
  have hTd : Differentiable ℂ T := T.differentiable
  refine ⟨hU.preimage T.continuous, hUd.preimage T.toHomeomorph.isOpenMap, ?_, fun s₀ => ?_⟩
  · exact isHolomorphicOn_iff_differentiableOn_scalar.mpr
      ((isHolomorphicOn_iff_differentiableOn_scalar.mp hhol).comp hTd.differentiableOn
        (mapsTo_preimage T U))
  · obtain ⟨W, hW, hcW, hs₀W, g, h, hg, hgnz, hh, hgh⟩ := hloc (T s₀)
    refine ⟨T ⁻¹' W, hW.preimage T.continuous, ?_, hs₀W, g ∘ T, h ∘ T, ?_, ?_, ?_, ?_⟩
    · have h1 : T ⁻¹' W = T.symm '' W := by
        ext x
        constructor
        · intro hx
          exact ⟨T x, hx, by simp⟩
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
      rw [h1]
      exact hcW.image _ T.symm.continuous.continuousOn
    · exact (hg.differentiableOn.comp hTd.differentiableOn (mapsTo_preimage T W)).mdifferentiableOn
    · obtain ⟨s, hs, hgs⟩ := hgnz
      exact ⟨T.symm s, by simpa using hs, by simpa using hgs⟩
    · exact isHolomorphicOn_iff_differentiableOn_scalar.mpr
        ((isHolomorphicOn_iff_differentiableOn_scalar.mp hh).comp hTd.differentiableOn
          (mapsTo_preimage T W))
    · intro s hs
      exact hgh (T s) hs

/-- A function meromorphic in one chart `e₀ : ℂⁿ ≃ X` is meromorphic in linear coordinates. -/
theorem isMeromorphicInCoordinatesOn_of_chart {X : Type*} [AddCommGroup X] [Module ℂ X] {n : ℕ}
    (e₀ : (Fin n → ℂ) ≃ₗ[ℂ] X) {φ : (Fin n → ℂ) → ℂ} {D' : Set (Fin n → ℂ)}
    (hφ : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) φ D') :
    IsMeromorphicInCoordinatesOn (φ ∘ e₀.symm) (e₀.symm ⁻¹' D') := by
  refine ⟨LinearEquiv.finiteDimensional e₀, fun n' e => ?_⟩
  exact isMeromorphicOn_comp_continuousLinearEquiv hφ (e.trans e₀.symm).toContinuousLinearEquiv

end Transport

/-! ## Linear algebra -/

section LinearAlgebra

/-- Coordinates in a linearly independent finite family of functions are linear combinations of
finitely many point evaluations (after `exists_continuousLinearMap_leftInverse`). -/
theorem exists_eval_leftInverse {Γ : Type} {ι : Type*} [Fintype ι] (b : ι → Γ → ℂ)
    (hb : LinearIndependent ℂ b) :
    ∃ (κ : Type) (_ : Fintype κ) (pts : κ → Γ) (Λ : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)),
      ∀ c : ι → ℂ, Λ (fun j => ∑ i, c i * b i (pts j)) = c := by
  classical
  set T : (ι → ℂ) →ₗ[ℂ] (Γ → ℂ) := Fintype.linearCombination ℂ b with hT
  have hTinj : Function.Injective T := hb.fintypeLinearCombination_injective
  let L : Γ → Module.Dual ℂ (ι → ℂ) := fun x => (LinearMap.proj x).comp T
  have hL : ∀ x c, L x c = T c x := fun _ _ => rfl
  have hspan : Submodule.span ℂ (Set.range L) = ⊤ := by
    have hco : (Submodule.span ℂ (Set.range L)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      rw [Submodule.mem_dualCoannihilator] at hc
      have hzero : T c = 0 := by
        funext x
        rw [← hL]
        exact hc _ (Submodule.subset_span ⟨x, rfl⟩)
      have : c = 0 := hTinj (by rw [hzero, map_zero])
      rw [this]
      exact Submodule.zero_mem _
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range L)),
      hco, Submodule.dualAnnihilator_bot]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' ℂ L
  have : Finite κ := hli.finite_of_isNoetherian
  let rS : (Γ → ℂ) →ₗ[ℂ] (κ → ℂ) := LinearMap.funLeft ℂ ℂ a
  have hker : LinearMap.ker (rS ∘ₗ T) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have hvan : ∀ k : κ, L (a k) c = 0 := fun k => by
      rw [hL]
      exact congrFun hc k
    have hall : ∀ f : Module.Dual ℂ (ι → ℂ), f c = 0 := by
      intro f
      have hf : f ∈ Submodule.span ℂ (Set.range (L ∘ a)) := by
        rw [hsp, hspan]
        exact Submodule.mem_top
      have hle : Submodule.span ℂ (Set.range (L ∘ a)) ≤
          LinearMap.ker (Module.Dual.eval ℂ (ι → ℂ) c) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        exact hvan k
      exact hle hf
    rw [Submodule.mem_bot]
    exact (Module.forall_dual_apply_eq_zero_iff ℂ c).1 hall
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (rS ∘ₗ T) hker
  refine ⟨κ, Fintype.ofFinite κ, a, ψ, fun c => ?_⟩
  have h1 : (ψ ∘ₗ (rS ∘ₗ T)) c = c := by rw [hψ]; rfl
  have h2 : (rS ∘ₗ T) c = fun j => ∑ i, c i * b i (a j) := by
    funext j
    simp [rS, hT, Fintype.linearCombination_apply, Finset.sum_apply, LinearMap.funLeft_apply]
  rw [← h2]
  exact h1

/-- The Gram form `∑ i, ∑ i', x i · conj (x i') · Gm i i'`. -/
def gramForm {m : ℕ} (Gm : Fin m → Fin m → ℂ) (x : Fin m → ℂ) : ℂ :=
  ∑ i, ∑ i', x i * (starRingEnd ℂ) (x i') * Gm i i'

/-- The vector on `Fin m` obtained by summing `y` over the fibres of `a : κ → Fin m`. -/
def fiberSum {m : ℕ} {κ : Type*} [Fintype κ] (a : κ → Fin m) (y : κ → ℂ) : Fin m → ℂ :=
  fun i => ∑ k ∈ Finset.univ.filter (fun k => a k = i), y k

theorem sum_fiberSum_mul {m : ℕ} {κ : Type*} [Fintype κ] (a : κ → Fin m) (y : κ → ℂ)
    (z : Fin m → ℂ) : ∑ i, fiberSum a y i * z i = ∑ k, y k * z (a k) := by
  classical
  simp only [fiberSum, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ a (fun k => y k * z (a k))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k hk => ?_
  rw [(Finset.mem_filter.mp hk).2]

theorem fiberSum_smul {m : ℕ} {κ : Type*} [Fintype κ] (a : κ → Fin m) (t : ℂ) (y : κ → ℂ) :
    fiberSum a (t • y) = t • fiberSum a y := by
  funext i
  simp [fiberSum, Finset.mul_sum]

theorem gramForm_smul {m : ℕ} (Gm : Fin m → Fin m → ℂ) (t : ℂ) (x : Fin m → ℂ) :
    gramForm Gm (t • x) = t * (starRingEnd ℂ) t * gramForm Gm x := by
  simp only [gramForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  ring

/-- Coercivity of a positive definite Gram form on a linearly independent subfamily. -/
theorem exists_coercive {m : ℕ} {Γ κ : Type*} [Fintype κ] (ψ : Fin m → Γ → ℂ)
    (Gm : Fin m → Fin m → ℂ) (a : κ → Fin m) (hli : LinearIndependent ℂ (fun k => ψ (a k)))
    (hgram : ∀ x : Fin m → ℂ, 0 ≤ gramForm Gm x ∧ (gramForm Gm x = 0 ↔ ∑ i, x i • ψ i = 0)) :
    ∃ ε > (0 : ℝ), ∀ y : κ → ℂ, ε * ‖y‖ ^ 2 ≤ (gramForm Gm (fiberSum a y)).re := by
  classical
  set q : (κ → ℂ) → ℝ := fun y => (gramForm Gm (fiberSum a y)).re with hqdef
  have hpos : ∀ y : κ → ℂ, y ≠ 0 → 0 < q y := by
    intro y hy
    obtain ⟨h0, hiff⟩ := hgram (fiberSum a y)
    rw [Complex.nonneg_iff] at h0
    rcases h0.1.lt_or_eq with hlt | heq
    · exact hlt
    exfalso
    have hz : gramForm Gm (fiberSum a y) = 0 := Complex.ext heq.symm h0.2.symm
    have hs := hiff.mp hz
    have hs' : ∑ k, y k • ψ (a k) = 0 := by
      have h1 : ∑ i, fiberSum a y i • ψ i = ∑ k, y k • ψ (a k) := by
        funext g
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact sum_fiberSum_mul a y (fun i => ψ i g)
      rw [← h1]
      exact hs
    exact hy (funext fun k => Fintype.linearIndependent_iff.mp hli y hs' k)
  have hcont : Continuous q := by
    simp only [hqdef, gramForm, fiberSum]
    fun_prop
  have hhom : ∀ (r : ℝ) (y : κ → ℂ), q ((r : ℂ) • y) = r ^ 2 * q y := by
    intro r y
    simp only [hqdef, fiberSum_smul, gramForm_smul, Complex.conj_ofReal]
    rw [show (r : ℂ) * r = ((r ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  by_cases hκ : Nonempty κ
  · have hK : IsCompact (sphere (0 : κ → ℂ) 1) := isCompact_sphere 0 1
    have hne : (sphere (0 : κ → ℂ) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
    have hy₀ne : y₀ ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy₀
      exact zero_ne_one hy₀
    refine ⟨q y₀, hpos y₀ hy₀ne, fun y => ?_⟩
    rcases eq_or_ne y 0 with rfl | hy
    · simp [hqdef, fiberSum, gramForm]
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set u : κ → ℂ := ((‖y‖⁻¹ : ℝ) : ℂ) • y with hudef
    have hu : u ∈ sphere (0 : κ → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hudef, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hny), inv_mul_cancel₀ hny.ne']
    have hyu : y = ((‖y‖ : ℝ) : ℂ) • u := by
      rw [hudef, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hny.ne', Complex.ofReal_one,
        one_smul]
    have h1 : q y₀ ≤ q u := hmin hu
    have h2 : q y = ‖y‖ ^ 2 * q u := by
      conv_lhs => rw [hyu]
      exact hhom _ _
    show q y₀ * ‖y‖ ^ 2 ≤ q y
    rw [h2]
    nlinarith [sq_nonneg ‖y‖]
  · refine ⟨1, one_pos, fun y => ?_⟩
    have : IsEmpty κ := not_nonempty_iff.mp hκ
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    simp [fiberSum, gramForm]

end LinearAlgebra

/-! ## The core argument -/

section Core

variable {n : ℕ}

/-- The zero set of a product of nonzero affine linear forms on `ℂⁿ` has dense complement. -/
theorem dense_setOf_prod_ne_zero {ι : Type*} [Fintype ι] (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hne : ∀ k, ∃ x : Fin n → ℂ, ℓ k x ≠ 0) (s₀ : Fin n → ℂ) :
    Dense {s : Fin n → ℂ | ∏ k, ℓ k (s - s₀) ≠ 0} := by
  set S : ι → Set (Fin n → ℂ) := fun k => {s | ℓ k (s - s₀) ≠ 0} with hSdef
  have hcont : ∀ k, Continuous fun s : Fin n → ℂ => ℓ k (s - s₀) := fun k =>
    (ℓ k).continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
  have hopen : ∀ k, IsOpen (S k) := fun k => isOpen_ne_fun (hcont k) continuous_const
  have hdense : ∀ k, Dense (S k) := by
    intro k
    rw [Metric.dense_iff]
    intro v r hr
    by_cases hv : v ∈ S k
    · exact ⟨v, mem_ball_self hr, hv⟩
    obtain ⟨x, hx⟩ := hne k
    set c : ℝ := r / (2 * (‖x‖ + 1)) with hcdef
    have hc : 0 < c := by positivity
    refine ⟨v + (c : ℂ) • x, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg hc.le]
      have h1 : c * ‖x‖ ≤ c * (‖x‖ + 1) := by nlinarith [norm_nonneg x]
      have h2 : c * (‖x‖ + 1) = r / 2 := by
        rw [hcdef]; field_simp
      linarith
    · have hv0 : ℓ k (v - s₀) = 0 := not_not.mp hv
      show ℓ k (v + (c : ℂ) • x - s₀) ≠ 0
      rw [show v + (c : ℂ) • x - s₀ = (v - s₀) + (c : ℂ) • x by abel, map_add, map_smul, hv0,
        zero_add, smul_eq_mul]
      exact mul_ne_zero (by exact_mod_cast hc.ne') hx
  have h := dense_iInter_of_isOpen hopen hdense
  convert h using 1
  ext s
  simp [hSdef, Finset.prod_ne_zero_iff]

/-- **Holomorphy near `iℝⁿ` from an isometry identity** (Mœglin–Waldspurger IV.3.12, second
step; Lapid 2011, pp.328–329), in one chart. Let `∑ i, coeff i s • ψ i` be a finite expansion
with coefficients meromorphic on `ℂⁿ` with domain `D`. Suppose that the Gram form `gramForm Gm` is
positive definite modulo linear relations of the `ψ i` (`hgram`), that every meromorphic
representation `∑ i, c i s • ψ i` of the same function satisfies `gramForm Gm (c s) = K₀` at the
imaginary points of its domain (`hiso`), and that near every imaginary point `s₀` a product of
affine linear forms `ℓ k (s - s₀)`, real and nonzero on `ℝⁿ`, times the expansion is holomorphic
(`hRH`). Then the function has a meromorphic representation whose domain contains `iℝⁿ`. -/
theorem exists_holomorphic_on_imaginary_of_isometry {m : ℕ} {Γ : Type} (ψ : Fin m → Γ → ℂ)
    (Gm : Fin m → Fin m → ℂ)
    (hgram : ∀ x : Fin m → ℂ, 0 ≤ gramForm Gm x ∧ (gramForm Gm x = 0 ↔ ∑ i, x i • ψ i = 0))
    (coeff : Fin m → (Fin n → ℂ) → ℂ) {D : Set (Fin n → ℂ)}
    (hcoeff : ∀ i, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (coeff i) D) (K₀ : ℂ)
    (hiso : ∀ (c : Fin m → (Fin n → ℂ) → ℂ) (D' : Set (Fin n → ℂ)),
      (∀ i, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (c i) D') →
      (∀ s ∈ D ∩ D', ∀ g, ∑ i, c i s * ψ i g = ∑ i, coeff i s * ψ i g) →
      ∀ s ∈ D', (∀ t, (s t).re = 0) → gramForm Gm (fun i => c i s) = K₀)
    (hRH : ∀ s₀ : Fin n → ℂ, (∀ t, (s₀ t).re = 0) →
      ∃ (ι : Type) (_ : Fintype ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ),
        (∀ k (x : Fin n → ℝ), (ℓ k (fun t => (x t : ℂ))).im = 0) ∧
        (∀ k, ∃ x : Fin n → ℝ, ℓ k (fun t => (x t : ℂ)) ≠ 0) ∧
        ∃ W : Set (Fin n → ℂ), IsOpen W ∧ s₀ ∈ W ∧ ∀ g : Γ, ∃ h : (Fin n → ℂ) → ℂ,
          DifferentiableOn ℂ h W ∧ ∀ s ∈ W, s ∈ D →
            h s = (∏ k, ℓ k (s - s₀)) * ∑ i, coeff i s * ψ i g) :
    ∃ (c : Fin m → (Fin n → ℂ) → ℂ) (D' : Set (Fin n → ℂ)),
      {s | ∀ t, (s t).re = 0} ⊆ D' ∧ (∀ i, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (c i) D') ∧
      ∀ s ∈ D ∩ D', ∀ g, ∑ i, c i s * ψ i g = ∑ i, coeff i s * ψ i g := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨fun i => i.elim0, univ, subset_univ _, fun i => i.elim0, fun s _ g => by simp⟩
  have hDo : IsOpen D := (hcoeff ⟨0, hm⟩).1
  have hDd : Dense D := (hcoeff ⟨0, hm⟩).2.1
  -- A linearly independent subfamily with the same span, and coordinates in it.
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ ψ
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  obtain ⟨P, _, pts, Λ, hΛ⟩ := exists_eval_leftInverse (fun k => ψ (a k)) hli
  set d : κ → (Fin n → ℂ) → ℂ := fun k s => Λ (fun j => ∑ i, coeff i s * ψ i (pts j)) k
    with hddef
  have hΛexp : ∀ (v : P → ℂ) k, Λ v k = ∑ j, v j * Λ (fun j' => if j = j' then 1 else 0) k := by
    intro v k
    rw [LinearMap.pi_apply_eq_sum_univ Λ v, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hd_lin : ∀ k s, d k s = ∑ i, coeff i s * Λ (fun j => ψ i (pts j)) k := by
    intro k s
    have h1 : (fun j => ∑ i, coeff i s * ψ i (pts j)) =
        ∑ i, coeff i s • (fun j => ψ i (pts j)) := by
      funext j
      simp [Finset.sum_apply]
    simp only [hddef, h1, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hd_expand : ∀ s g, ∑ i, coeff i s * ψ i g = ∑ k, d k s * ψ (a k) g := by
    intro s g
    have hmem : (∑ i, coeff i s • ψ i) ∈ Submodule.span ℂ (Set.range (ψ ∘ a)) := by
      rw [hsp]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
    have hdc : (fun k => d k s) = c := by
      have h1 := hΛ c
      have h2 : (fun j => ∑ k, c k * ψ (a k) (pts j)) =
          (fun j => ∑ i, coeff i s * ψ i (pts j)) := by
        funext j
        have := congrFun hc (pts j)
        simpa [Finset.sum_apply] using this
      rw [h2] at h1
      funext k
      exact congrFun h1 k
    calc ∑ i, coeff i s * ψ i g = (∑ i, coeff i s • ψ i) g := by simp [Finset.sum_apply]
      _ = (∑ k, c k • (ψ ∘ a) k) g := by rw [hc]
      _ = ∑ k, c k * ψ (a k) g := by simp [Finset.sum_apply]
      _ = ∑ k, d k s * ψ (a k) g := by simp only [← hdc]
  have hd_mero : ∀ k, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (d k) D := by
    intro k
    have h1 := IsMeromorphicOn.sum Finset.univ hDo hDd
      (a := fun i s => coeff i s * Λ (fun j => ψ i (pts j)) k)
      (fun i _ => (hcoeff i).mul_const _)
    convert h1 using 1
    funext s
    rw [hd_lin, Finset.sum_apply]
  -- Maximal extensions of the coordinates.
  set Ω : κ → Set (Fin n → ℂ) := fun k => extensionDomain (d k) D with hΩdef
  set dmax : κ → (Fin n → ℂ) → ℂ := fun k => maximalExtension (d k) D with hdmaxdef
  set Ωa : Set (Fin n → ℂ) := ⋂ k, Ω k with hΩadef
  have hΩa_open : IsOpen Ωa := isOpen_iInter_of_finite fun k => isOpen_extensionDomain
  have hDΩa : D ⊆ Ωa := fun s hs =>
    mem_iInter.mpr fun k => subset_extensionDomain (hd_mero k) hs
  have hΩa_dense : Dense Ωa := hDd.mono hDΩa
  have hdmax_mero : ∀ k, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (dmax k) Ωa := fun k =>
    (isMeromorphicOn_maximalExtension (hd_mero k)).restrict_domain hΩa_open hΩa_dense
      (iInter_subset _ k)
  have hdmax_D : ∀ k, ∀ s ∈ D, dmax k s = d k s := fun k s hs =>
    maximalExtension_eqOn_self (hd_mero k) hs
  set c : Fin m → (Fin n → ℂ) → ℂ := fun i s => fiberSum a (fun k => dmax k s) i with hcdef
  have hc_mero : ∀ i, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (c i) Ωa := by
    intro i
    have h1 := IsMeromorphicOn.sum (Finset.univ.filter fun k => a k = i) hΩa_open hΩa_dense
      (fun k _ => hdmax_mero k)
    convert h1 using 1
    funext s
    simp [hcdef, fiberSum, Finset.sum_apply]
  have hc_sum : ∀ s g, ∑ i, c i s * ψ i g = ∑ k, dmax k s * ψ (a k) g := fun s g =>
    sum_fiberSum_mul a (fun k => dmax k s) (fun i => ψ i g)
  have hc_agree : ∀ s ∈ D ∩ Ωa, ∀ g, ∑ i, c i s * ψ i g = ∑ i, coeff i s * ψ i g := by
    intro s hs g
    rw [hc_sum, hd_expand]
    exact Finset.sum_congr rfl fun k _ => by rw [hdmax_D k s hs.1]
  have hQ := hiso c Ωa hc_mero hc_agree
  -- A bound on the imaginary points of the common domain.
  obtain ⟨ε, hε, hcoer⟩ := exists_coercive ψ Gm a hli hgram
  set Cb : ℝ := Real.sqrt (K₀.re / ε) with hCbdef
  have hbd : ∀ s ∈ Ωa, (∀ t, (s t).re = 0) → ∀ k, ‖dmax k s‖ ≤ Cb := by
    intro s hs hsre k
    have h1 := hcoer (fun k => dmax k s)
    have h2 : gramForm Gm (fiberSum a (fun k => dmax k s)) = K₀ := hQ s hs hsre
    rw [h2] at h1
    have h3 : ‖(fun k => dmax k s)‖ ≤ Cb := by
      rw [show ‖(fun k => dmax k s)‖ = Real.sqrt (‖(fun k => dmax k s)‖ ^ 2) by
        rw [Real.sqrt_sq (norm_nonneg _)]]
      exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hε]; linarith)
    exact (norm_le_pi_norm (fun k => dmax k s) k).trans h3
  -- Every imaginary point lies in every extension domain.
  have hslice : ∀ s₀ : Fin n → ℂ, (∀ t, (s₀ t).re = 0) → ∀ k, s₀ ∈ Ω k := by
    intro s₀ hs₀
    obtain ⟨ι, hι, ℓ, hreal, hne, W, hW, hs₀W, hH⟩ := hRH s₀ hs₀
    choose h hh hhe using hH
    set L : (Fin n → ℂ) → ℂ := fun s => ∏ k, ℓ k (s - s₀) with hLdef
    have hℓd : ∀ k, Differentiable ℂ (ℓ k) := fun k => by
      simpa using (LinearMap.toContinuousLinearMap (ℓ k)).differentiable
    have hk : ∀ k, Differentiable ℂ (fun s : Fin n → ℂ => ℓ k (s - s₀)) := fun k =>
      (hℓd k).comp (differentiable_id.sub_const s₀)
    have hLd : Differentiable ℂ L := fun s =>
      (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun k (s : Fin n → ℂ) => ℓ k (s - s₀))
        fun k _ => ((hk k) s).hasFDerivAt).differentiableAt
    set H : κ → (Fin n → ℂ) → ℂ := fun k s =>
      ∑ j, h (pts j) s * Λ (fun j' => if j = j' then 1 else 0) k with hHdef
    have hHd : ∀ k, DifferentiableOn ℂ (H k) W := fun k => by
      have h1 := DifferentiableOn.sum (u := Finset.univ)
        (A := fun j s => h (pts j) s * Λ (fun j' => if j = j' then 1 else 0) k)
        fun j _ => (hh (pts j)).mul_const _
      convert h1 using 1
      funext s
      simp [hHdef, Finset.sum_apply]
    have hHeq : ∀ k, ∀ s ∈ W, s ∈ D → H k s = L s * d k s := by
      intro k s hsW hsD
      simp only [hHdef, hddef]
      rw [hΛexp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hhe (pts j) s hsW hsD]
      ring
    set O : Set (Fin n → ℂ) := W ∩ {s | L s ≠ 0} with hOdef
    have hO : IsOpen O := hW.inter (isOpen_ne_fun hLd.continuous continuous_const)
    have hquot : ∀ k, DifferentiableOn ℂ (fun s => H k s / L s) O := fun k y hy => by
      have h1 : DifferentiableWithinAt ℂ (fun y => H k y * (L y)⁻¹) O y :=
        ((hHd k y hy.1).mono inter_subset_left).mul ((hLd y).differentiableWithinAt.inv hy.2)
      simpa only [div_eq_mul_inv] using h1
    have hquot_eq : ∀ k, EqOn (fun s => H k s / L s) (d k) (O ∩ D) := by
      intro k s hs
      simp only
      rw [hHeq k s hs.1.1 hs.2, mul_div_cancel_left₀ _ hs.1.2]
    have hOΩ : ∀ k, O ⊆ Ω k := fun k s hs => ⟨O, hO, hs, _, hquot k, hquot_eq k⟩
    have hdmaxO : ∀ k, EqOn (dmax k) (fun s => H k s / L s) O := fun k =>
      maximalExtension_eqOn hDd hO (hquot k) (hquot_eq k)
    have hbound : ∀ k, ∀ s ∈ W, (∀ t, (s t).re = 0) → L s ≠ 0 → ‖H k s‖ ≤ Cb * ‖L s‖ := by
      intro k s hsW hsre hLs
      have hsO : s ∈ O := ⟨hsW, hLs⟩
      have hsΩa : s ∈ Ωa := mem_iInter.mpr fun k' => hOΩ k' hsO
      have h1 := hbd s hsΩa hsre k
      rw [hdmaxO k hsO] at h1
      simp only at h1
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hLs)] at h1
      exact h1
    intro k
    obtain ⟨δ, hδ, c', hc', hc'eq⟩ := exists_differentiableOn_mul_eq_of_norm_le_on_imaginary
      ℓ hreal hne hs₀ hW hs₀W (hHd k) (C := Cb) (hbound k)
    set N : Set (Fin n → ℂ) := ball s₀ δ ∩ W with hNdef
    have hN : IsOpen N := isOpen_ball.inter hW
    refine ⟨N, hN, ⟨mem_ball_self hδ, hs₀W⟩, c', hc'.mono inter_subset_left, ?_⟩
    have hdense : Dense {s | L s ≠ 0} := dense_setOf_prod_ne_zero ℓ
      (fun k => by obtain ⟨x, hx⟩ := hne k; exact ⟨_, hx⟩) s₀
    have hND : IsOpen (N ∩ D) := hN.inter hDo
    have heq1 : EqOn c' (d k) ((N ∩ D) ∩ {s | L s ≠ 0}) := by
      rintro s ⟨⟨⟨hsb, hsW⟩, hsD⟩, hLs⟩
      have h1 := hc'eq s hsb
      rw [hHeq k s hsW hsD] at h1
      exact mul_left_cancel₀ hLs h1
    exact heq1.of_subset_closure
      ((hc'.mono inter_subset_left).continuousOn.mono inter_subset_left)
      ((isHolomorphicOn_iff_differentiableOn_scalar.mp (hd_mero k).2.2.1).continuousOn.mono
        inter_subset_right)
      inter_subset_left (hdense.open_subset_closure_inter hND)
  exact ⟨c, Ωa, fun s hs => mem_iInter.mpr fun k => hslice s hs k, hc_mero, hc_agree⟩

/-- A meromorphic function on `ℂⁿ` remains meromorphic on a smaller open dense domain. -/
theorem isMeromorphicOn_restrict {f : (Fin n → ℂ) → ℂ} {U V : Set (Fin n → ℂ)}
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f U) (hV : IsOpen V) (hdV : Dense V) (hVU : V ⊆ U) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f V :=
  hf.restrict_domain hV hdV hVU

end Core

end Langlands.Analysis.Meromorphic.ImaginaryHyperplane
