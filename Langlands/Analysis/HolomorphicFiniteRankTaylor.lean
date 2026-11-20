import Langlands.Analysis.HolomorphicFiniteRank
import Langlands.Analysis.HolomorphicTaylor
import Langlands.Global.EisensteinJetFiniteVectors
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Finite rank of Taylor coefficient profiles -/

noncomputable section

open Set Filter Matrix
open scoped Topology

namespace Langlands.Analysis

open Global.EisensteinJet (coefficientSpan mem_coefficientSpan)

variable {X A : Type*}

/-- Clear the determinant denominator in the point-evaluation coordinates of a profile. -/
def profileCramer {n : ℕ} (p : Fin n → X) (f : Fin n → X → ℂ) (g : X → ℂ) : Fin n → ℂ :=
  (profileMatrix p f).cramer (g ∘ p)

private theorem profileCramer_reconstruct {n : ℕ} (p : Fin n → X) (f : Fin n → X → ℂ)
    (g : X → ℂ) (hg : g ∈ Submodule.span ℂ (range f)) :
    (profileMatrix p f).det • g = Fintype.linearCombination ℂ f (profileCramer p f g) := by
  rw [← Fintype.range_linearCombination] at hg
  obtain ⟨v, rfl⟩ := hg
  have hC : profileCramer p f (Fintype.linearCombination ℂ f v) = (profileMatrix p f).det • v := by
    unfold profileCramer
    rw [show (Fintype.linearCombination ℂ f v) ∘ p = profileMatrix p f *ᵥ v
      from (profileMatrix_mulVec p f v).symm,
      cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rw [hC, map_smul]

private theorem analyticOnNhd_profileCramer {n : ℕ} (p : Fin n → X)
    (f : Fin n → ℂ → X → ℂ) (g : ℂ → X → ℂ) {U : Set ℂ}
    (hf : ∀ j x, AnalyticOnNhd ℂ (fun t => f j t x) U)
    (hg : ∀ x, AnalyticOnNhd ℂ (fun t => g t x) U) (j : Fin n) :
    AnalyticOnNhd ℂ (fun t => profileCramer p (fun i => f i t) (g t) j) U := by
  classical
  let h (i : Fin n) : ℂ → X → ℂ := if i = j then g else f i
  have hM (t : ℂ) : (profileMatrix p (fun i => f i t)).updateCol j (g t ∘ p) =
      profileMatrix p (fun i => h i t) := by
    ext r c
    simp only [Matrix.updateCol_apply, profileMatrix, Matrix.of_apply]
    by_cases hc : c = j <;> simp [hc, h]
  simp only [profileCramer, cramer_apply, hM]
  exact analyticOnNhd_profileMatrix_det p h (fun i x => by
    by_cases hi : i = j
    · simpa only [h, ite_eq_left hi] using hg x
    · simpa only [h, ite_eq_right hi] using hf i x)

private theorem coeff_mem_span_of_mul {n : ℕ} (h : Fin n → X → PowerSeries ℂ)
    (d : PowerSeries ℂ) (hd : d ≠ 0) (g : X → PowerSeries ℂ) (b : Fin n → PowerSeries ℂ)
    (he : ∀ x, d * g x = ∑ j, b j * h j x) (N : ℕ) :
    (fun x => PowerSeries.coeff N (g x)) ∈ coefficientSpan
      (fun j k x => PowerSeries.coeff k (h j x)) (d.order.toNat + N + 1) := by
  let e := d.order.toNat
  let c := PowerSeries.coeff e d
  have hc : c ≠ 0 := PowerSeries.coeff_order hd
  let C := coefficientSpan (fun j k x => PowerSeries.coeff k (h j x)) (e + N + 1)
  suffices hh : ∀ k ≤ N, (fun x => PowerSeries.coeff k (g x)) ∈ C by exact hh N le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    let A := Finset.antidiagonal (e + k)
    have he₀ : (e, k) ∈ A := Finset.mem_antidiagonal.mpr rfl
    let w (p : ℕ × ℕ) : X → ℂ := PowerSeries.coeff p.1 d • fun x => PowerSeries.coeff p.2 (g x)
    have hrest : (∑ p ∈ A.erase (e, k), w p) ∈ C := by
      apply Submodule.sum_mem
      intro p hp
      have hneq : p ≠ (e, k) := (Finset.mem_erase.mp hp).1
      have heq := Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hp)
      by_cases hlt : p.1 < e
      · simp only [w, PowerSeries.coeff_of_lt_order_toNat _ hlt, zero_smul]
        exact C.zero_mem
      · have hlt' : e < p.1 := by
          refine lt_of_le_of_ne (Nat.le_of_not_gt hlt) fun he' => hneq ?_
          exact Prod.ext he'.symm (by omega)
        have hsmall : p.2 < k := by omega
        exact C.smul_mem _ (ih _ hsmall (hsmall.le.trans hk))
    have hrhs : (fun x => PowerSeries.coeff (e + k) (d * g x)) ∈ C := by
      simp_rw [he, map_sum, PowerSeries.coeff_mul]
      rw [show (fun x => ∑ j, ∑ p ∈ A,
          PowerSeries.coeff p.1 (b j) * PowerSeries.coeff p.2 (h j x)) =
          ∑ j, ∑ p ∈ A,
            (PowerSeries.coeff p.1 (b j) • fun x => PowerSeries.coeff p.2 (h j x)) from by
        funext x
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
      refine C.sum_mem fun j _ => C.sum_mem fun p hp => C.smul_mem _ ?_
      apply mem_coefficientSpan
      have heq := Finset.mem_antidiagonal.mp hp
      omega
    have hsplit : (fun x => PowerSeries.coeff (e + k) (d * g x)) =
        (∑ p ∈ A.erase (e, k), w p) + c • (fun x => PowerSeries.coeff k (g x)) := by
      rw [← show w (e, k) = c • (fun x => PowerSeries.coeff k (g x)) from rfl,
        Finset.sum_erase_add _ _ he₀]
      funext x
      simp only [PowerSeries.coeff_mul, A, w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hh := C.sub_mem hrhs hrest
    rw [hsplit, add_sub_cancel_left] at hh
    simpa only [inv_smul_smul₀ hc] using C.smul_mem c⁻¹ hh

/-- The degree `N` coefficient profiles have finite-dimensional span, even at
parameters where the rank of the original family drops. -/
theorem finiteDimensional_span_profileTaylor (f : A → ℂ → X → ℂ) {U W : Set ℂ}
    (hU : IsPreconnected U) (hUo : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U) (hne : W.Nonempty)
    (hf : ∀ a x, AnalyticOnNhd ℂ (fun t => f a t x) U)
    (hfin : ∀ t ∈ W, FiniteDimensional ℂ (Submodule.span ℂ (range fun a => f a t)))
    {z : ℂ} (hz : z ∈ U) (N : ℕ) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun a x =>
      iteratedDeriv N (fun t => f a t x) z / (N.factorial : ℂ))) := by
  obtain ⟨n, s, p, t₁, ht₁, ht₁ne, hspan⟩ := exists_spanningProfileMatrix f hU hW hWU hne hf hfin
  let Δ (t : ℂ) := (profileMatrix p (fun j => f (s j) t)).det
  let Q (a : A) (j : Fin n) (t : ℂ) := profileCramer p (fun i => f (s i) t) (f a t) j
  have hΔ : AnalyticOnNhd ℂ Δ U := analyticOnNhd_profileMatrix_det _ _ (fun j => hf (s j))
  have hQ (a : A) (j : Fin n) : AnalyticOnNhd ℂ (Q a j) U :=
    analyticOnNhd_profileCramer _ _ _ (fun j => hf (s j)) (hf a) j
  have hrelation (a : A) (x : X) :
      (fun t => Δ t * f a t x) =ᶠ[𝓝 z] fun t => ∑ j, Q a j t * f (s j) t x := by
    let V := U ∩ Δ ⁻¹' ({0}ᶜ : Set ℂ)
    have hV : IsOpen V := hΔ.continuousOn.isOpen_inter_preimage hUo isClosed_singleton.isOpen_compl
    have ht : t₁ ∈ V := ⟨ht₁, ht₁ne⟩
    have hEq : (fun t => Δ t * f a t x) =ᶠ[𝓝 t₁] fun t => ∑ j, Q a j t * f (s j) t x := by
      filter_upwards [hV.mem_nhds ht] with t ht
      have h := congrFun (profileCramer_reconstruct p (fun j => f (s j) t) (f a t)
        (hspan t ht.1 ht.2 a)) x
      simpa only [Δ, Q, Fintype.linearCombination_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_apply] using h
    have h₁ : AnalyticOnNhd ℂ (fun t => Δ t * f a t x) U := hΔ.mul (hf a x)
    have h₂ : AnalyticOnNhd ℂ (fun t => ∑ j, Q a j t * f (s j) t x) U :=
      Finset.analyticOnNhd_fun_sum _ fun j _ => (hQ a j).mul (hf (s j) x)
    filter_upwards [hUo.mem_nhds hz] with t ht
    exact h₁.eqOn_of_preconnected_of_eventuallyEq h₂ hU ht₁ hEq ht
  let d₀ : holomorphicAtSubring z := ⟨Δ, hΔ z hz⟩
  let f₀ (a : A) (x : X) : holomorphicAtSubring z := ⟨fun t => f a t x, hf a x z hz⟩
  let q₀ (a : A) (j : Fin n) : holomorphicAtSubring z := ⟨Q a j, hQ a j z hz⟩
  let T := holomorphicTaylor z
  have hd : T d₀ ≠ 0 := holomorphicTaylor_ne_zero z d₀
    (hΔ.analyticOrderAt_ne_top_of_isPreconnected hU ht₁ hz
      (((hΔ t₁ ht₁).analyticOrderAt_eq_zero.mpr ht₁ne) ▸ ENat.zero_ne_top))
  have hformal (a : A) (x : X) :
      T d₀ * T (f₀ a x) = ∑ j, T (q₀ a j) * T (f₀ (s j) x) := by
    simp_rw [← map_mul, ← map_sum]
    ext k
    rw [coeff_holomorphicTaylor, coeff_holomorphicTaylor]
    congr 1
    have hR : ((holomorphicAtSubring z).subtype (∑ j, q₀ a j * f₀ (s j) x)) =
        fun t => ∑ j, Q a j t * f (s j) t x := by
      rw [map_sum]
      funext t
      rw [Finset.sum_apply]
      rfl
    change iteratedDeriv k (fun t => Δ t * f a t x) z =
      iteratedDeriv k ((holomorphicAtSubring z).subtype (∑ j, q₀ a j * f₀ (s j) x)) z
    rw [hR]
    exact (hrelation a x).iteratedDeriv_eq k
  let H (j : Fin n) (x : X) := T (f₀ (s j) x)
  let S := coefficientSpan (fun j k x => PowerSeries.coeff k (H j x)) ((T d₀).order.toNat + N + 1)
  let : FiniteDimensional ℂ S := Module.Finite.span_of_finite ℂ (finite_range _)
  have hle : Submodule.span ℂ (range fun a x =>
      iteratedDeriv N (fun t => f a t x) z / (N.factorial : ℂ)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change (fun x => iteratedDeriv N (fun t => f a t x) z / (N.factorial : ℂ)) ∈ S
    have hc (x : X) : PowerSeries.coeff N (T (f₀ a x)) =
        iteratedDeriv N (fun t => f a t x) z / (N.factorial : ℂ) :=
      coeff_holomorphicTaylor z (f₀ a x) N
    rw [← funext hc]
    exact coeff_mem_span_of_mul H (T d₀) hd (fun x => T (f₀ a x)) (fun j => T (q₀ a j))
      (hformal a) N
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end Langlands.Analysis
