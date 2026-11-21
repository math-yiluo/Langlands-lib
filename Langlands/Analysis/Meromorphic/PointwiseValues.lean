import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Analysis.ProductCoordinateScalarization

/-! # Meromorphic functions with values in a space of functions with pointwise convergence

Meromorphy (Bernstein–Lapid §3.1, `Langlands.Analysis.Meromorphic.IsMeromorphicOn`) for
functions on `ℂᵐ` with values in the product `ι → ℂ`, with Mathlib's product topology (the
topology of pointwise convergence):

* a continuous linear form on `ι → ℂ` is a finite linear combination of coordinates, so a
  function into `ι → ℂ` is holomorphic exactly when its coordinates are;
* a family of scalar functions with local meromorphic data whose denominators do not depend on
  the member of the family glues to one meromorphic function with values in `ι → ℂ`;
* local meromorphic data survive finite linear combinations with entire coefficients and
  division by an entire function that vanishes on no nonempty open set. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open scoped Manifold Topology
open Set

section Forms

variable {ι : Type*}

open Classical in
/-- A continuous linear form on the product `ι → ℂ` (product topology) is a finite linear
combination of coordinates. -/
theorem exists_finset_continuousLinearMap_pi_eq_sum (μ : (ι → ℂ) →L[ℂ] ℂ) :
    ∃ S : Finset ι, ∀ x : ι → ℂ, μ x = ∑ i ∈ S, x i * μ (Pi.single i 1) := by
  classical
  obtain ⟨S, L, hL⟩ := Langlands.Analysis.continuousLinearMap_product_factors
    (F := fun _ : ι => ℂ) (μ.restrictScalars ℝ)
  refine ⟨S, fun x => ?_⟩
  set y : ι → ℂ := ∑ i ∈ S, x i • Pi.single i (1 : ℂ) with hy
  have hres : (fun i : S => y i.val) = fun i : S => x i.val := by
    funext i
    simp only [hy, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [i.property]
  have h1 : μ x = μ y := by
    have hx := hL x
    have hy' := hL y
    simp only [ContinuousLinearMap.coe_restrictScalars'] at hx hy'
    rw [hx, hy', hres]
  rw [h1, hy, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

variable {m : ℕ}

/-- A function on `ℂᵐ` with values in `ι → ℂ` whose coordinates are complex differentiable on
`U` is holomorphic on `U`. -/
theorem isHolomorphicOn_pi_of_differentiableOn {f : (Fin m → ℂ) → ι → ℂ} {U : Set (Fin m → ℂ)}
    (h : ∀ i, DifferentiableOn ℂ (fun s => f s i) U) :
    IsHolomorphicOn 𝓘(ℂ, Fin m → ℂ) f U := by
  classical
  intro μ
  obtain ⟨S, hS⟩ := exists_finset_continuousLinearMap_pi_eq_sum μ
  have hμ : (fun s => μ (f s)) = fun s => ∑ i ∈ S, f s i * μ (Pi.single i 1) :=
    funext fun s => hS (f s)
  rw [hμ]
  exact mdifferentiableOn_iff_differentiableOn.2
    (DifferentiableOn.fun_sum fun i _ => (h i).mul_const _)

/-- A holomorphic function on `ℂᵐ` with values in `ι → ℂ` has differentiable coordinates. -/
theorem differentiableOn_apply_of_isHolomorphicOn {f : (Fin m → ℂ) → ι → ℂ}
    {U : Set (Fin m → ℂ)} (h : IsHolomorphicOn 𝓘(ℂ, Fin m → ℂ) f U) (i : ι) :
    DifferentiableOn ℂ (fun s => f s i) U :=
  mdifferentiableOn_iff_differentiableOn.1 (h (ContinuousLinearMap.proj i))

end Forms

section Gluing

variable {m : ℕ} {ι : Type*}

/-- Gluing with values in `ι → ℂ`: a family `φ i` of scalar functions on `ℂᵐ` with local
meromorphic data at every point (denominators independent of `i`) gives one function
`s ↦ (φ i s)ᵢ` that is meromorphic with values in `ι → ℂ`, for the product topology. Its domain
of holomorphy is the set of points near which every `φ i` is holomorphic. -/
theorem exists_isMeromorphicOn_pi_of_local {φ : ι → (Fin m → ℂ) → ℂ}
    (hφ : ∀ s₀, HasLocalMeromorphicData φ s₀) :
    ∃ U : Set (Fin m → ℂ), IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun s i => φ i s) U := by
  set U : Set (Fin m → ℂ) :=
    {s | ∃ O : Set (Fin m → ℂ), IsOpen O ∧ s ∈ O ∧ ∀ i, DifferentiableOn ℂ (φ i) O} with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    rintro s ⟨O, hOo, hsO, hO⟩
    exact ⟨O, fun t ht => ⟨O, hOo, ht, hO⟩, hOo, hsO⟩
  have hsub : ∀ {D : Set (Fin m → ℂ)}, IsOpen D → (∀ i, DifferentiableOn ℂ (φ i) D) → D ⊆ U :=
    fun hDo hD s hs => ⟨_, hDo, hs, hD⟩
  have hdiff : ∀ i, DifferentiableOn ℂ (φ i) U := by
    rintro i s ⟨O, hOo, hsO, hO⟩
    exact ((hO i).differentiableAt (hOo.mem_nhds hsO)).differentiableWithinAt
  have hUd : Dense U := by
    intro s₀
    obtain ⟨D, W, hDo, hD, -, -, hs₀W, hWD, -⟩ := hφ s₀
    exact closure_mono (hsub hDo hD) (hWD hs₀W)
  refine ⟨U, hUo, hUd, isHolomorphicOn_pi_of_differentiableOn hdiff, fun s₀ => ?_⟩
  obtain ⟨D, W, hDo, hD, hWo, hWc, hs₀W, hWD, q, hq, hq0, hqh⟩ := hφ s₀
  choose h hh hqφ using hqh
  refine ⟨W, hWo, hWc, hs₀W, q, fun s i => h i s, mdifferentiableOn_iff_differentiableOn.2 hq,
    hq0, isHolomorphicOn_pi_of_differentiableOn hh, ?_⟩
  have hcl : U ∩ W ⊆ closure (D ∩ W) := by
    intro s hs
    have := hWo.inter_closure ⟨hs.2, hWD hs.2⟩
    rwa [inter_comm] at this
  intro s hs
  funext i
  refine EqOn.of_subset_closure (s := D ∩ W) (t := U ∩ W) (f := fun s => q s * φ i s)
    (g := h i) (fun t ht => hqφ i t ht) ?_ ?_ (fun t ht => ⟨hsub hDo hD ht.1, ht.2⟩) hcl hs
  · exact ((hq.mono inter_subset_right).continuousOn).mul
      ((hdiff i).mono inter_subset_left).continuousOn
  · exact ((hh i).mono inter_subset_right).continuousOn

/-- An entire function on `ℂᵐ` that is nonzero at one point is nonzero somewhere in every
nonempty open set. -/
theorem exists_ne_zero_of_differentiable {g : (Fin m → ℂ) → ℂ} (hg : Differentiable ℂ g)
    {s₁ : Fin m → ℂ} (hs₁ : g s₁ ≠ 0) {O : Set (Fin m → ℂ)} (hO : IsOpen O)
    (hOne : O.Nonempty) : ∃ s ∈ O, g s ≠ 0 :=
  exists_ne_zero_of_differentiableOn isOpen_univ isPreconnected_univ hg.differentiableOn
    ⟨s₁, mem_univ _, hs₁⟩ hO (subset_univ _) hOne

/-- Local meromorphic data survive finite linear combinations with entire coefficients and
division by an entire function `den` that is nonzero at some point: if `φ` has local data at
`s₀` and `Ψ x = den⁻¹ * ∑_{k < B} coef x k * φ (idx x k)`, then `Ψ` has local data at `s₀`, with
denominator the old one times `den`. -/
theorem HasLocalMeromorphicData.combination {φ : ι → (Fin m → ℂ) → ℂ} {s₀ : Fin m → ℂ}
    (hφ : HasLocalMeromorphicData φ s₀) {κ : Type*} {Ψ : κ → (Fin m → ℂ) → ℂ}
    {den : (Fin m → ℂ) → ℂ} (hden : Differentiable ℂ den) {s₁ : Fin m → ℂ} (hs₁ : den s₁ ≠ 0)
    (B : ℕ) (coef : κ → ℕ → (Fin m → ℂ) → ℂ) (hcoef : ∀ x k, Differentiable ℂ (coef x k))
    (idx : κ → ℕ → ι)
    (hΨ : ∀ x s, Ψ x s = (den s)⁻¹ * ∑ k ∈ Finset.range B, coef x k s * φ (idx x k) s) :
    HasLocalMeromorphicData Ψ s₀ := by
  obtain ⟨D, W, hDo, hD, hWo, hWc, hs₀W, hWD, q, hq, ⟨t₁, ht₁W, hqt₁⟩, hqh⟩ := hφ
  choose h hh hqφ using hqh
  set Z : Set (Fin m → ℂ) := {s | den s ≠ 0} with hZ
  have hZo : IsOpen Z := isOpen_ne_fun hden.continuous continuous_const
  have hZd : Dense Z := by
    refine dense_iff_inter_open.2 fun O hO hOne => ?_
    obtain ⟨s, hsO, hs⟩ := exists_ne_zero_of_differentiable hden hs₁ hO hOne
    exact ⟨s, hsO, hs⟩
  refine ⟨D ∩ Z, W, hDo.inter hZo, fun x => ?_, hWo, hWc, hs₀W, ?_, fun s => q s * den s,
    hq.mul hden.differentiableOn, ?_, fun x => ⟨fun s => ∑ k ∈ Finset.range B,
      coef x k s * h (idx x k) s, ?_, ?_⟩⟩
  · have hsum : DifferentiableOn ℂ
        (fun s => ∑ k ∈ Finset.range B, coef x k s * φ (idx x k) s) (D ∩ Z) :=
      DifferentiableOn.fun_sum fun k _ =>
        ((hcoef x k).differentiableOn.mul (hD (idx x k))).mono inter_subset_left
    have hinv : DifferentiableOn ℂ (fun s => (den s)⁻¹) (D ∩ Z) :=
      hden.differentiableOn.inv fun s hs => hs.2
    refine (hinv.mul hsum).congr fun s _ => ?_
    exact hΨ x s
  · intro s hs
    have h1 : D ⊆ closure (D ∩ Z) := by
      have := hZd.open_subset_closure_inter hDo
      exact this
    exact closure_minimal h1 isClosed_closure (hWD hs)
  · have hO : IsOpen (W ∩ {s | q s ≠ 0}) :=
      hq.continuousOn.isOpen_inter_preimage hWo isOpen_ne
    obtain ⟨s, ⟨hsW, hqs⟩, hdens⟩ :=
      exists_ne_zero_of_differentiable hden hs₁ hO ⟨t₁, ht₁W, hqt₁⟩
    exact ⟨s, hsW, mul_ne_zero hqs hdens⟩
  · exact DifferentiableOn.fun_sum fun k _ => (hcoef x k).differentiableOn.mul (hh (idx x k))
  · rintro s ⟨⟨hsD, hsZ⟩, hsW⟩
    rw [hΨ x s, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hqφ (idx x k) s ⟨hsD, hsW⟩]
    have hd : den s ≠ 0 := hsZ
    field_simp

end Gluing

end Langlands.Analysis.Meromorphic
