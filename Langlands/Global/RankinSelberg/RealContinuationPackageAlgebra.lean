import Langlands.Global.RankinSelberg.RealUniformContinuationReduction

/-! # Algebra of continuation packages

Products, finite sums, scalar multiples, translations and right half-plane changes of the
meromorphic continuation and multiplied-out functional equation `RealJacquet.ContinuationPackage`.
-/

noncomputable section

open Filter Set Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

namespace ContinuationPackage

variable {Z Zd L Ld E Z₁ Zd₁ L₁ Ld₁ E₁ Z₂ Zd₂ L₂ Ld₂ E₂ : ℂ → ℂ} {sign sign₁ sign₂ : ℂ}

/-- The zero functions satisfy every continuation package. -/
theorem zero (L Ld E : ℂ → ℂ) (sign : ℂ) :
    ContinuationPackage (fun _ => 0) (fun _ => 0) L Ld E sign :=
  ⟨0, fun _ => 0, fun _ => 0, MeromorphicOn.const 0, MeromorphicOn.const 0,
    fun _ _ => rfl, fun _ _ => rfl, Eventually.of_forall fun _ => by ring⟩

/-- Products of two packages form a package for the products of all data. -/
theorem mul (h₁ : ContinuationPackage Z₁ Zd₁ L₁ Ld₁ E₁ sign₁)
    (h₂ : ContinuationPackage Z₂ Zd₂ L₂ Ld₂ E₂ sign₂) :
    ContinuationPackage (fun s => Z₁ s * Z₂ s) (fun s => Zd₁ s * Zd₂ s)
      (fun s => L₁ s * L₂ s) (fun s => Ld₁ s * Ld₂ s) (fun s => E₁ s * E₂ s)
      (sign₁ * sign₂) := by
  obtain ⟨σ₁, M₁, Md₁, hM₁, hMd₁, hZ₁, hZd₁, hE₁⟩ := h₁
  obtain ⟨σ₂, M₂, Md₂, hM₂, hMd₂, hZ₂, hZd₂, hE₂⟩ := h₂
  refine ⟨max σ₁ σ₂, fun s => M₁ s * M₂ s, fun s => Md₁ s * Md₂ s, hM₁.mul hM₂,
    hMd₁.mul hMd₂, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · dsimp only
    rw [hZ₁ s (lt_of_le_of_lt (le_max_left _ _) hs), hZ₂ s (lt_of_le_of_lt (le_max_right _ _) hs)]
  · dsimp only
    rw [hZd₁ s (lt_of_le_of_lt (le_max_left _ _) hs),
      hZd₂ s (lt_of_le_of_lt (le_max_right _ _) hs)]
  · filter_upwards [hE₁, hE₂] with s e₁ e₂
    linear_combination (L₂ s * Md₂ (1 - s)) * e₁ +
      (sign₁ * E₁ s * Ld₁ (1 - s) * M₁ s) * e₂

/-- Sums of two packages with the same factors and sign form a package. -/
theorem add (h₁ : ContinuationPackage Z₁ Zd₁ L Ld E sign)
    (h₂ : ContinuationPackage Z₂ Zd₂ L Ld E sign) :
    ContinuationPackage (fun s => Z₁ s + Z₂ s) (fun s => Zd₁ s + Zd₂ s) L Ld E sign := by
  obtain ⟨σ₁, M₁, Md₁, hM₁, hMd₁, hZ₁, hZd₁, hE₁⟩ := h₁
  obtain ⟨σ₂, M₂, Md₂, hM₂, hMd₂, hZ₂, hZd₂, hE₂⟩ := h₂
  refine ⟨max σ₁ σ₂, fun s => M₁ s + M₂ s, fun s => Md₁ s + Md₂ s, hM₁.add hM₂,
    hMd₁.add hMd₂, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · dsimp only
    rw [hZ₁ s (lt_of_le_of_lt (le_max_left _ _) hs), hZ₂ s (lt_of_le_of_lt (le_max_right _ _) hs)]
  · dsimp only
    rw [hZd₁ s (lt_of_le_of_lt (le_max_left _ _) hs),
      hZd₂ s (lt_of_le_of_lt (le_max_right _ _) hs)]
  · filter_upwards [hE₁, hE₂] with s e₁ e₂
    linear_combination e₁ + e₂

/-- Finite sums of packages with the same factors and sign form a package. -/
theorem sum {ι : Type*} (S : Finset ι) {Z Zd : ι → ℂ → ℂ}
    (h : ∀ i ∈ S, ContinuationPackage (Z i) (Zd i) L Ld E sign) :
    ContinuationPackage (fun s => ∑ i ∈ S, Z i s) (fun s => ∑ i ∈ S, Zd i s) L Ld E sign := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero L Ld E sign
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    exact add (h j (Finset.mem_insert_self j S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Multiplying both integral functions by the same constant preserves a package. -/
theorem const_mul (c : ℂ) (h : ContinuationPackage Z Zd L Ld E sign) :
    ContinuationPackage (fun s => c * Z s) (fun s => c * Zd s) L Ld E sign := by
  obtain ⟨σ, M, Md, hM, hMd, hZ, hZd, hE⟩ := h
  refine ⟨σ, fun s => c * M s, fun s => c * Md s, (MeromorphicOn.const c).mul hM,
    (MeromorphicOn.const c).mul hMd, fun s hs => by dsimp only; rw [hZ s hs],
    fun s hs => by dsimp only; rw [hZd s hs], ?_⟩
  filter_upwards [hE] with s e
  linear_combination c * e

/-- Multiplying only the dual integral function by a constant multiplies the sign by it. -/
theorem dual_const_mul (c : ℂ) (h : ContinuationPackage Z Zd L Ld E sign) :
    ContinuationPackage Z (fun s => c * Zd s) L Ld E (c * sign) := by
  obtain ⟨σ, M, Md, hM, hMd, hZ, hZd, hE⟩ := h
  refine ⟨σ, M, fun s => c * Md s, hM, (MeromorphicOn.const c).mul hMd, hZ,
    fun s hs => by dsimp only; rw [hZd s hs], ?_⟩
  filter_upwards [hE] with s e
  linear_combination c * e

/-- A package only depends on the integral functions on some right half-plane. -/
theorem congr_right {Z' Zd' : ℂ → ℂ} (h : ContinuationPackage Z Zd L Ld E sign) (τ : ℝ)
    (hZ' : ∀ s : ℂ, τ < s.re → Z' s = Z s) (hZd' : ∀ s : ℂ, τ < s.re → Zd' s = Zd s) :
    ContinuationPackage Z' Zd' L Ld E sign := by
  obtain ⟨σ, M, Md, hM, hMd, hZ, hZd, hE⟩ := h
  refine ⟨max σ τ, M, Md, hM, hMd, fun s hs => ?_, fun s hs => ?_, hE⟩
  · rw [hZ' s (lt_of_le_of_lt (le_max_right _ _) hs), hZ s (lt_of_le_of_lt (le_max_left _ _) hs)]
  · rw [hZd' s (lt_of_le_of_lt (le_max_right _ _) hs),
      hZd s (lt_of_le_of_lt (le_max_left _ _) hs)]

/-- A package only depends on the factors and the sign off a discrete set, through the
multiplied-out equation. -/
theorem congr_factors {L' Ld' E' : ℂ → ℂ} {sign' : ℂ}
    (h : ContinuationPackage Z Zd L Ld E sign)
    (hf : ∀ᶠ s in codiscrete ℂ, ∀ A B : ℂ,
      L s * A = sign * E s * Ld (1 - s) * B → L' s * A = sign' * E' s * Ld' (1 - s) * B) :
    ContinuationPackage Z Zd L' Ld' E' sign' := by
  obtain ⟨σ, M, Md, hM, hMd, hZ, hZd, hE⟩ := h
  refine ⟨σ, M, Md, hM, hMd, hZ, hZd, ?_⟩
  filter_upwards [hE, hf] with s e f
  exact f _ _ e

private theorem eventually_codiscrete_comp_add {p : ℂ → Prop} (w : ℂ)
    (h : ∀ᶠ t in codiscrete ℂ, p t) : ∀ᶠ s in codiscrete ℂ, p (s + w) := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE] at h ⊢
  intro x
  have ht : Tendsto (fun s : ℂ => s + w) (𝓝[≠] x) (𝓝[≠] (x + w)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((continuous_id.add continuous_const).tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [mem_compl_iff, mem_singleton_iff, add_left_inj] at hs ⊢
      exact hs
  exact ht.eventually (h (x + w))

private theorem meromorphicOn_comp_add {M : ℂ → ℂ} (hM : MeromorphicOn M univ) (w : ℂ) :
    MeromorphicOn (fun s => M (s + w)) univ := fun z _ =>
  (hM (z + w) (mem_univ _)).comp_analyticAt (g := fun s : ℂ => s + w)
    (analyticAt_id.add analyticAt_const)

/-- Translating the primal variable by `w` and the dual variable by `-w` preserves a
package, with translated factors. -/
theorem shift (w : ℂ) (h : ContinuationPackage Z Zd L Ld E sign) :
    ContinuationPackage (fun s => Z (s + w)) (fun s => Zd (s - w)) (fun s => L (s + w))
      (fun s => Ld (s - w)) (fun s => E (s + w)) sign := by
  obtain ⟨σ, M, Md, hM, hMd, hZ, hZd, hE⟩ := h
  have h₁ (s : ℂ) (hs : σ + |w.re| < s.re) : σ < (s + w).re := by
    rw [Complex.add_re]
    linarith [neg_abs_le w.re]
  have h₂ (s : ℂ) (hs : σ + |w.re| < s.re) : σ < (s - w).re := by
    rw [Complex.sub_re]
    linarith [le_abs_self w.re]
  refine ⟨σ + |w.re|, fun s => M (s + w), fun s => Md (s - w), meromorphicOn_comp_add hM w, ?_,
    fun s hs => hZ _ (h₁ s hs), fun s hs => hZd _ (h₂ s hs), ?_⟩
  · simpa only [sub_eq_add_neg] using meromorphicOn_comp_add hMd (-w)
  · filter_upwards [eventually_codiscrete_comp_add w hE] with s hs
    rw [show 1 - s - w = 1 - (s + w) by ring]
    exact hs

end ContinuationPackage

/-- A constant multiple of a finite sum of products of two families of packages with common
factors and signs, with one further constant on the dual side, is a package for the product
factors. This is the shape of Jacquet's corank-one recursion after compact projection. -/
def ContinuationPackageSumProductStatement : Prop :=
  ∀ {ι : Type} (S : Finset ι) (A Ad B Bd : ι → ℂ → ℂ) (L₁ Ld₁ E₁ L₂ Ld₂ E₂ : ℂ → ℂ)
    (sign₁ sign₂ b d : ℂ),
    (∀ i ∈ S, ContinuationPackage (A i) (Ad i) L₁ Ld₁ E₁ sign₁) →
    (∀ i ∈ S, ContinuationPackage (B i) (Bd i) L₂ Ld₂ E₂ sign₂) →
    ContinuationPackage (fun s => b * ∑ i ∈ S, A i s * B i s)
      (fun s => d * (b * ∑ i ∈ S, Ad i s * Bd i s))
      (fun s => L₁ s * L₂ s) (fun s => Ld₁ s * Ld₂ s) (fun s => E₁ s * E₂ s)
      (d * (sign₁ * sign₂))

theorem continuationPackageSumProduct : ContinuationPackageSumProductStatement := by
  intro ι S A Ad B Bd L₁ Ld₁ E₁ L₂ Ld₂ E₂ sign₁ sign₂ b d hA hB
  exact ContinuationPackage.dual_const_mul d (ContinuationPackage.const_mul b
    (ContinuationPackage.sum S fun i hi => ContinuationPackage.mul (hA i hi) (hB i hi)))

end Langlands.Global.RankinSelbergGlobal.RealJacquet
