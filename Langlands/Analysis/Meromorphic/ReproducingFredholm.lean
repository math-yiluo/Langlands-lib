import Langlands.Analysis.Meromorphic.FredholmExactFiber
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Finite type after a reproducing smoothing operator

The analytic step of Bernstein–Lapid §7.6, on supplied operators: add the
reproducing equation to the Hilbert system and use an exact-base-fiber envelope.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set ContinuousLinearMap
open scoped Manifold

section WeakHolomorphy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  {S : Set M}

/-- Base-point injectivity of a weakly holomorphic finite-dimensional family persists
on a neighbourhood if a family of continuous scalar tests separates points. -/
theorem IsHolomorphicOperatorFamilyOn.exists_open_injective {n : ℕ}
    {ℓ : M → (Fin n → ℂ) →L[ℂ] V} (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ S)
    (hS : IsOpen S) {s₀ : M} (hs₀ : s₀ ∈ S) (hinj : Function.Injective (ℓ s₀))
    {J : Type*} (ev : J → V →L[ℂ] ℂ) (hev : ∀ v, (∀ j, ev j v = 0) → v = 0) :
    ∃ U ⊆ S, IsOpen U ∧ s₀ ∈ U ∧ ∀ s ∈ U, Function.Injective (ℓ s) := by
  classical
  let D := Fin n → ℂ
  let W : J → Set D := fun j => {x | ev j (ℓ s₀ x) ≠ 0}
  have hW (j : J) : IsOpen (W j) :=
    isOpen_ne_fun ((ev j).continuous.comp (ℓ s₀).continuous) continuous_const
  have hcov : Metric.sphere (0 : D) 1 ⊆ ⋃ j, W j := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
    by_contra! h
    have hz : ∀ j, ev j (ℓ s₀ x) = 0 := fun j => by
      by_contra hj
      exact h (mem_iUnion.2 ⟨j, hj⟩)
    have hx0 : x = 0 := hinj (by simpa only [map_zero] using hev (ℓ s₀ x) hz)
    simp [hx0] at hn
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : D) 1).elim_finite_subcover W hW hcov
  let Q := (↑t : Type _) → ℂ
  let P : M → D →L[ℂ] Q := fun s => ContinuousLinearMap.pi (fun j : (↑t : Type _) => ev j ∘L ℓ s)
  have hPi (s : M) (x : D) (j : ↑t) : P s x j = ev j (ℓ s x) := rfl
  have hP₀ : Function.Injective (P s₀) := by
    have hk : (P s₀).ker = ⊥ := by
      refine le_antisymm (fun x hx => ?_) bot_le
      rw [Submodule.mem_bot]
      by_contra hx0
      let a : ℂ := (‖x‖ : ℂ)⁻¹
      have hnorm : ‖a • x‖ = 1 := by
        rw [norm_smul, show ‖a‖ = ‖x‖⁻¹ by simp [a]]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
      have hm : a • x ∈ Metric.sphere (0 : D) 1 := by simpa [Metric.mem_sphere, dist_zero_right]
      obtain ⟨j, hj⟩ := mem_iUnion.mp (ht hm)
      obtain ⟨hjt, hne⟩ := mem_iUnion.mp hj
      have hz : P s₀ (a • x) (⟨j, hjt⟩ : ↑t) = 0 := by
        have hzero : P s₀ x = 0 := hx
        rw [map_smul, hzero, smul_zero]
        rfl
      exact hne (hPi s₀ (a • x) ⟨j, hjt⟩ ▸ hz)
    exact LinearMap.ker_eq_bot.mp hk
  let e : (D →L[ℂ] Q) ≃L[ℂ] (Fin n → Q) := ContinuousLinearEquiv.piRing (Fin n)
  have hPc : ContinuousOn P S := by
    have hc : ContinuousOn (fun s => e (P s)) S := by
      apply continuousOn_pi.2
      intro i
      apply continuousOn_pi.2
      intro j
      change ContinuousOn (fun s => ev j (ℓ s (Pi.single i 1))) S
      exact (hℓ (Pi.single i 1) (ev j)).continuousOn
    exact e.symm.continuous.comp_continuousOn hc |>.congr fun s _ => (e.symm_apply_apply _).symm
  let U := S ∩ P ⁻¹' {f | Function.Injective f}
  refine ⟨U, inter_subset_left, hPc.isOpen_inter_preimage hS ContinuousLinearMap.isOpen_injective,
    ⟨hs₀, hP₀⟩, ?_⟩
  intro s hs x y hxy
  apply hs.2
  funext j
  rw [hPi, hPi, hxy]

/-- A finite combination of fixed continuous linear smoothing maps with holomorphic
scalar coefficients preserves weak holomorphy of an applied operator family. -/
theorem IsHolomorphicOperatorFamilyOn.finset_smul_comp
    [ContinuousAdd V] [ContinuousConstSMul ℂ V]
    {B H : Type*} [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    {ℓ : M → H →L[ℂ] B} (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ S)
    {ι : Type*} (t : Finset ι) (K : ι → B →L[ℂ] V) {b : ι → M → ℂ}
    (hb : ∀ i ∈ t, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (b i) S) :
    IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) (fun s => (∑ i ∈ t, b i s • K i) ∘L ℓ s) S := by
  intro v ψ
  have h : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (∑ i ∈ t, fun s => b i s * ψ (K i (ℓ s v))) S :=
    MDifferentiableOn.sum fun i hi => (hb i hi).mul (hℓ v (ψ ∘L K i))
  refine h.congr fun s _ => ?_
  simp [Finset.sum_apply, smul_eq_mul]

end WeakHolomorphy

universe uE uM uB uC uV uι uJ

/-- A Fredholm system augmented by a reproducing equation has smoothed solutions of
finite type. The smoothing maps have holomorphic scalar coefficients and reproduce
injectively on the joint kernel at the base point, as witnessed by `S₀ x = 0 → T₀ x = 0`. -/
def ReproducingFredholmFiniteTypeStatement : Prop :=
  ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
    {B : Type uB} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {C : Type uC} [NormedAddCommGroup C] [NormedSpace ℂ C]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousConstSMul ℂ V]
    {ι : Type uι} [Fintype ι] {J : Type uJ}
    {A : M → B →L[ℂ] C} {T : M → B →L[ℂ] B} {S : Set M}, IsOpen S →
    IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) A S →
    IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) T S →
    ∀ {s₀ : M}, s₀ ∈ S → ∀ D : C →L[ℂ] B,
    IsCompactOperator (D ∘L A s₀ - ContinuousLinearMap.id ℂ B) →
    ∀ (K : ι → B →L[ℂ] V) (b : ι → M → ℂ) (ev : J → V →L[ℂ] ℂ),
    (∀ v, (∀ j, ev j v = 0) → v = 0) →
    (∀ i, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (b i) S) →
    (∀ x, (∑ i, b i s₀ • K i) x = 0 → T s₀ x = 0) →
    ∃ U ⊆ S, IsOpen U ∧ s₀ ∈ U ∧ IsFiniteTypeOn 𝓘(ℂ, E)
      (fun s => (fun x => (∑ i, b i s • K i : B →L[ℂ] V) x) ''
        {x | A s x = 0 ∧ T s x = x}) U

/-- The analytic finite-type transfer for a Fredholm system with a reproducing equation. -/
theorem reproducingFredholmFiniteType :
    ReproducingFredholmFiniteTypeStatement.{uE, uM, uB, uC, uV, uι, uJ} := by
  intro E _ _ _ M _ _ _ B _ _ _ C _ _ V _ _ _ _ _ ι _ J A T S hS hA hT s₀ hs₀ D hD K b ev hev hb hKT
  let F : M → B →L[ℂ] C × B := fun s => (A s).prod (ContinuousLinearMap.id ℂ B - T s)
  have hF : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) F S := by
    intro v ψ
    let ψ₁ := ψ ∘L ContinuousLinearMap.inl ℂ C B
    let ψ₂ := ψ ∘L ContinuousLinearMap.inr ℂ C B
    refine ((hA v ψ₁).add ((mdifferentiableOn_const (c := ψ₂ v)).sub (hT v ψ₂))).congr fun s _ => ?_
    change ψ (A s v, v - T s v) = ψ₁ (A s v) + (ψ₂ v - ψ₂ (T s v))
    rw [← map_sub]
    change ψ (A s v, v - T s v) = ψ (A s v, 0) + ψ (0, v - T s v)
    rw [← map_add]
    simp
  let D' := D ∘L ContinuousLinearMap.fst ℂ C B
  have hD' : IsCompactOperator (D' ∘L F s₀ - ContinuousLinearMap.id ℂ B) := hD
  obtain ⟨U, hUS, hUo, hsU, n, ℓ, hℓ, hℓi, hℓk, hℓ₀⟩ :=
    exactFiberFredholmCriterion hS hF hs₀ D' hD'
  let Λ : M → (Fin n → ℂ) →L[ℂ] V := fun s => (∑ i, b i s • K i) ∘L ℓ s
  have hΛ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) Λ U :=
    hℓ.finset_smul_comp Finset.univ K (fun i _ => (hb i).mono hUS)
  have hΛ₀ : Function.Injective (Λ s₀) := by
    have hk : (Λ s₀).ker = ⊥ := by
      refine le_antisymm (fun x hx => ?_) bot_le
      rw [Submodule.mem_bot]
      have hm : ℓ s₀ x ∈ (F s₀).ker := by
        change ℓ s₀ x ∈ ((F s₀).ker : Set B)
        rw [← hℓ₀]
        exact ⟨x, rfl⟩
      have hFm : F s₀ (ℓ s₀ x) = 0 := hm
      have hfixed : ℓ s₀ x - T s₀ (ℓ s₀ x) = 0 := congrArg Prod.snd hFm
      have hTzero : T s₀ (ℓ s₀ x) = 0 := hKT _ hx
      apply hℓi s₀ hsU
      simpa only [hTzero, sub_zero, map_zero] using hfixed
    exact LinearMap.ker_eq_bot.mp hk
  obtain ⟨U', hU'U, hU'o, hsU', hΛi⟩ := hΛ.exists_open_injective hUo hsU hΛ₀ ev hev
  refine ⟨U', hU'U.trans hUS, hU'o, hsU', n, Λ, fun x ψ => (hΛ x ψ).mono hU'U, hΛi, ?_⟩
  intro s hs y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hFx : F s x = 0 := by
    change (A s x, x - T s x) = (0, 0)
    exact Prod.ext hx.1 (sub_eq_zero.mpr hx.2.symm)
  obtain ⟨c, hc⟩ := hℓk s (hU'U hs) x hFx
  refine ⟨c, ?_⟩
  change (∑ i, b i s • K i) (ℓ s c) = (∑ i, b i s • K i) x
  rw [hc]

end Langlands.Analysis.Meromorphic
