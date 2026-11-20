import Langlands.Automorphic.ComplexPlaceParameterWeights
import Mathlib.Data.Fin.Tuple.Sort

/-! # Dominant integral weights of regular complex-place lists -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Automorphic.ComplexPlaceParameter

open Langlands.LocalFactor.Archimedean

private theorem nodup_shifted {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) :
    (List.ofFn fun i => (μ i : ℂ) + rho n i).Nodup := by
  apply List.nodup_ofFn.mpr
  have h : StrictAnti (fun i : Fin n => μ i - (i.val : ℤ)) := by
    intro i j hij
    have hle := hμ hij.le
    have hlt : i.val < j.val := hij
    change μ j - (j.val : ℤ) < μ i - (i.val : ℤ)
    omega
  intro i j hij
  apply h.injective
  apply Int.cast_injective (α := ℂ)
  push_cast
  unfold rho at hij
  linear_combination hij

private theorem mem_shifted {n : ℕ} {μ : Fin n → ℤ} {x : ℂ}
    (hx : x ∈ List.ofFn (fun i => (μ i : ℂ) + rho n i)) :
    ∃ p : ℤ, x = (p : ℂ) + ((n : ℂ) - 1) / 2 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  refine ⟨μ i - (i.val : ℤ), ?_⟩
  simp only [rho, Int.cast_sub, Int.cast_natCast]
  ring

/-- The shifted lists of two dominant integral weights meet Clozel's regularity condition. -/
theorem isClozelRegularAlgebraic_of_matchesDominant {n : ℕ} {ds : List ComplexCharacterData}
    {μz μzBar : Fin n → ℤ} (hz : Antitone μz) (hzBar : Antitone μzBar)
    (hm : MatchesHighestWeight n ds (fun i => (μz i : ℂ)) (fun i => (μzBar i : ℂ))) :
    IsClozelRegularAlgebraic n ds := by
  refine ⟨hm.1, ?_, hm.2.1.nodup_iff.mpr (nodup_shifted hz),
    hm.2.2.nodup_iff.mpr (nodup_shifted hzBar)⟩
  intro d hd
  obtain ⟨p, hp⟩ := mem_shifted (hm.2.1.mem_iff.mp (List.mem_map_of_mem hd))
  obtain ⟨q, hq⟩ := mem_shifted (hm.2.2.mem_iff.mp (List.mem_map_of_mem hd))
  exact ⟨p, q, hp, hq⟩

private theorem exists_dominant_shift {n : ℕ} {f : Fin n → ℂ}
    (hint : ∀ i, ∃ p : ℤ, f i = (p : ℂ) + ((n : ℂ) - 1) / 2)
    (hinj : Function.Injective f) :
    ∃ μ : Fin n → ℤ, Antitone μ ∧
      (List.ofFn f).Perm (List.ofFn fun i => (μ i : ℂ) + rho n i) := by
  choose p hp using hint
  have hpInj : Function.Injective p := fun i j hij => hinj (by rw [hp i, hp j, hij])
  let σ := Tuple.sort (fun i => OrderDual.toDual (p i))
  have hs : StrictMono (fun i => OrderDual.toDual (p (σ i))) :=
    (Tuple.monotone_sort (fun i => OrderDual.toDual (p i))).strictMono_of_injective
      (hpInj.comp σ.injective)
  let μ : Fin n → ℤ := fun i => p (σ i) + (i.val : ℤ)
  refine ⟨μ, ?_, ?_⟩
  · cases n with
    | zero => exact fun i => i.elim0
    | succ n =>
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      have h := hs (Fin.castSucc_lt_succ (i := i))
      change p (σ i.succ) < p (σ i.castSucc) at h
      change p (σ i.succ) + ((i.val + 1 : ℕ) : ℤ) ≤ p (σ i.castSucc) + (i.val : ℤ)
      omega
  · have hf : f ∘ σ = fun i => (μ i : ℂ) + rho n i := by
      funext i
      rw [Function.comp_apply, hp (σ i)]
      simp only [μ, Int.cast_add, Int.cast_natCast, rho]
      ring
    rw [← hf]
    exact (σ.ofFn_comp_perm f).symm

/-- At a complex place, sort each integral exponent list independently and subtract `ρ`. -/
theorem exists_matchesDominant_of_isClozelRegularAlgebraic {n : ℕ} {ds : List ComplexCharacterData}
    (h : IsClozelRegularAlgebraic n ds) :
    ∃ μz μzBar : Fin n → ℤ, Antitone μz ∧ Antitone μzBar ∧
      MatchesHighestWeight n ds (fun i => (μz i : ℂ)) (fun i => (μzBar i : ℂ)) := by
  obtain ⟨hlen, hint, hz, hzBar⟩ := h
  subst n
  have sorted (coord : ComplexCharacterData → ℂ)
      (hi : ∀ d ∈ ds, ∃ p : ℤ, coord d = (p : ℂ) + ((ds.length : ℂ) - 1) / 2)
      (hd : (ds.map coord).Nodup) :
      ∃ μ : Fin ds.length → ℤ, Antitone μ ∧
        (ds.map coord).Perm (List.ofFn fun i => (μ i : ℂ) + rho ds.length i) := by
    have hlist : List.ofFn (coord ∘ ds.get) = ds.map coord := by
      rw [← List.map_ofFn, List.ofFn_get]
    have hInj := List.nodup_ofFn.mp (hlist ▸ hd : (List.ofFn (coord ∘ ds.get)).Nodup)
    obtain ⟨μ, hμ, hm⟩ := exists_dominant_shift
      (fun i => hi (ds.get i) (List.get_mem ds i)) hInj
    exact ⟨μ, hμ, hlist ▸ hm⟩
  obtain ⟨μz, hμz, hmz⟩ := sorted ComplexCharacterData.zExponent
    (fun d hd => let ⟨p, _, hp, _⟩ := hint d hd; ⟨p, hp⟩) hz
  obtain ⟨μzBar, hμzBar, hmzBar⟩ := sorted ComplexCharacterData.zBarExponent
    (fun d hd => let ⟨_, q, _, hq⟩ := hint d hd; ⟨q, hq⟩) hzBar
  exact ⟨μz, μzBar, hμz, hμzBar, rfl, hmz, hmzBar⟩

end Langlands.Automorphic.ComplexPlaceParameter
