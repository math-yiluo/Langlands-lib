import Langlands.Automorphic.CuspidalWhittaker.AdelicCharacter
import Mathlib.Topology.LocallyConstant.Basic

/-! # Small integral multiples and uniform local constancy on the finite adeles

Every neighbourhood of `0` in `𝔸_f` contains `N Ô` for some positive integer `N`, every compact
subset of `𝔸_f` is contained in `d⁻¹ Ô` for a nonzero `d ∈ 𝒪`, and a locally constant compactly
supported function on `𝔸_f^n` is invariant under translation by `(N Ô)^n` for some `N`.
-/

noncomputable section
universe u
open NumberField Topology Filter
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

/-- Every neighbourhood of `0` in `𝔸_f` contains a positive integer: the integers `1, 2, …` lie
in the compact group `Ô`, so two of them are close (pigeonhole). -/
theorem exists_nat_mem_of_mem_nhds_zero {U : Set (FiniteAdeles F)} (hU : U ∈ 𝓝 0) :
    ∃ N : ℕ, 0 < N ∧ (N : FiniteAdeles F) ∈ U := by
  obtain ⟨V, hV, hVU⟩ := exists_nhds_half_neg hU
  obtain ⟨t, -, ht⟩ := (isCompact_integralFiniteAdeles F).elim_nhds_subcover
    (fun x => {y | y - x ∈ V}) (fun x _ => by
      have hc : Continuous fun y : FiniteAdeles F => y - x := continuous_id.sub continuous_const
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hV))
  have hmem : ∀ k : ℕ, ∃ x ∈ t, (k : FiniteAdeles F) - x ∈ V := by
    intro k
    have hk : (k : FiniteAdeles F) ∈ (integralFiniteAdeles F : Set (FiniteAdeles F)) :=
      natCast_mem _ k
    simpa using ht hk
  choose f hft hfV using hmem
  obtain ⟨k, -, l, -, hkl, hfkl⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (t.card + 1)) (t := t) (by simp) (f := f) (fun k _ => hft k)
  rcases lt_or_gt_of_ne hkl with h | h
  · refine ⟨l - k, Nat.sub_pos_of_lt h, ?_⟩
    have e : ((l - k : ℕ) : FiniteAdeles F) =
        ((l : FiniteAdeles F) - f l) - ((k : FiniteAdeles F) - f k) := by
      rw [hfkl, Nat.cast_sub h.le]
      ring
    rw [e]
    exact hVU _ (hfV l) _ (hfV k)
  · refine ⟨k - l, Nat.sub_pos_of_lt h, ?_⟩
    have e : ((k - l : ℕ) : FiniteAdeles F) =
        ((k : FiniteAdeles F) - f k) - ((l : FiniteAdeles F) - f l) := by
      rw [hfkl, Nat.cast_sub h.le]
      ring
    rw [e]
    exact hVU _ (hfV k) _ (hfV l)

/-- Every neighbourhood of `0` in `𝔸_f` contains `N Ô` for a positive integer `N`. -/
theorem exists_nat_mul_mem_of_mem_nhds_zero {W : Set (FiniteAdeles F)} (hW : W ∈ 𝓝 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ c ∈ integralFiniteAdeles F, (N : FiniteAdeles F) * c ∈ W := by
  have h0 : (0 : FiniteAdeles F) ∈ interior W := mem_interior_iff_mem_nhds.mpr hW
  have hn : IsOpen {p : FiniteAdeles F × FiniteAdeles F | p.1 * p.2 ∈ interior W} :=
    isOpen_interior.preimage continuous_mul
  obtain ⟨u, v, hu, -, hsu, htv, huv⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : FiniteAdeles F)))
    (isCompact_integralFiniteAdeles F) hn (by
      rintro ⟨a, c⟩ ⟨ha, -⟩
      have ha' : a = 0 := ha
      change a * c ∈ interior W
      rw [ha', zero_mul]
      exact h0)
  have hu0 : (0 : FiniteAdeles F) ∈ u := hsu (Set.mem_singleton 0)
  obtain ⟨N, hN, hNu⟩ := exists_nat_mem_of_mem_nhds_zero F (hu.mem_nhds hu0)
  refine ⟨N, hN, fun c hc => ?_⟩
  have hp : ((N : FiniteAdeles F), c) ∈ u ×ˢ v := Set.mk_mem_prod hNu (htv hc)
  have hm : ((N : FiniteAdeles F), c) ∈
      {p : FiniteAdeles F × FiniteAdeles F | p.1 * p.2 ∈ interior W} := huv hp
  rw [Set.mem_ofPred_eq] at hm
  exact interior_subset hm

theorem algebraMap_ringOfIntegers_mem (d : 𝓞 F) :
    algebraMap (𝓞 F) (FiniteAdeles F) d ∈ integralFiniteAdeles F := by
  have := algebraMap_integer_mem F d
  rwa [← IsScalarTower.algebraMap_apply] at this

/-- A compact subset of `𝔸_f` is contained in `d⁻¹ Ô` for some nonzero `d ∈ 𝒪`. -/
theorem exists_integer_mul_mem_of_isCompact {K : Set (FiniteAdeles F)} (hK : IsCompact K) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ K,
      algebraMap (𝓞 F) (FiniteAdeles F) d * a ∈ integralFiniteAdeles F := by
  classical
  have hex : ∀ a : FiniteAdeles F, ∃ d : 𝓞 F, d ≠ 0 ∧
      algebraMap (𝓞 F) (FiniteAdeles F) d * a ∈ integralFiniteAdeles F := by
    intro a
    obtain ⟨d, hd, h⟩ := exists_integer_mul_mem_adicCompletionIntegers a
    exact ⟨d, hd, (mem_integralFiniteAdeles F _).mpr fun v => h v⟩
  choose d hd hda using hex
  have hopen : ∀ a, IsOpen {b : FiniteAdeles F |
      algebraMap (𝓞 F) (FiniteAdeles F) (d a) * b ∈ integralFiniteAdeles F} := fun a =>
    (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul continuous_id)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun a => {b : FiniteAdeles F |
      algebraMap (𝓞 F) (FiniteAdeles F) (d a) * b ∈ integralFiniteAdeles F}) hopen
    (fun a _ => Set.mem_iUnion.mpr ⟨a, hda a⟩)
  refine ⟨∏ a ∈ t, d a, Finset.prod_ne_zero_iff.mpr fun a _ => hd a, fun b hb => ?_⟩
  obtain ⟨a, hat, hab⟩ := Set.mem_iUnion₂.mp (ht hb)
  rw [← Finset.mul_prod_erase t d hat, map_mul, mul_comm (algebraMap _ _ (d a)), mul_assoc]
  exact mul_mem (algebraMap_ringOfIntegers_mem F _) hab

/-- A locally constant compactly supported function on `𝔸_f^n` is invariant under
translation by `(N Ô)^n` for some positive integer `N`. -/
theorem exists_nat_invariant_of_isLocallyConstant {n : ℕ}
    (f : (Fin n → FiniteAdeles F) → ℂ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ N : ℕ, 0 < N ∧ ∀ x u : Fin n → FiniteAdeles F,
      (∀ j, ∃ c ∈ integralFiniteAdeles F, u j = (N : FiniteAdeles F) * c) →
        f (x + u) = f x := by
  classical
  -- a uniform neighbourhood of invariance
  have hU : ∀ x, {w : Fin n → FiniteAdeles F | f (x + w) = f x} ∈ 𝓝 0 := by
    intro x
    have hfib : IsOpen (f ⁻¹' {f x}) := hf.isOpen_fiber _
    have hc' : Continuous fun w : Fin n → FiniteAdeles F => x + w :=
      continuous_const.add continuous_id
    exact hc'.continuousAt.preimage_mem_nhds (hfib.mem_nhds (by simp))
  choose V hV hVU using fun x => exists_nhds_zero_half (hU x)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun x => {y | y - x ∈ V x})
    (fun x _ => by
      have hc' : Continuous fun y : Fin n → FiniteAdeles F => y - x :=
        continuous_id.sub continuous_const
      exact hc'.continuousAt.preimage_mem_nhds (by simpa using hV x))
  set W₀ := ⋂ x ∈ t, V x with hW₀
  have hW₀n : W₀ ∈ 𝓝 0 := (Filter.biInter_finset_mem t).mpr fun x _ => hV x
  set W := W₀ ∩ (fun w => -w) ⁻¹' W₀ with hWdef
  have hWn : W ∈ 𝓝 (0 : Fin n → FiniteAdeles F) :=
    Filter.inter_mem hW₀n (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hW₀n))
  have hinvK : ∀ y ∈ tsupport f, ∀ w ∈ W₀, f (y + w) = f y := by
    intro y hy w hw
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    have hwx : w ∈ V x := Set.mem_iInter₂.mp hw x hxt
    have h1 := hVU x _ hyx _ hwx
    have h2 := hVU x _ hyx _ (mem_of_mem_nhds (hV x))
    simp only [Set.mem_ofPred_eq, add_zero] at h1 h2
    rw [show x + (y - x + w) = y + w by abel] at h1
    rw [show x + (y - x) = y by abel] at h2
    rw [h1, h2]
  have hinv : ∀ y, ∀ w ∈ W, f (y + w) = f y := by
    intro y w hw
    by_cases hy : y ∈ tsupport f
    · exact hinvK y hy w hw.1
    · by_cases hyw : y + w ∈ tsupport f
      · have := hinvK (y + w) hyw (-w) hw.2
        rw [add_neg_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyw]
  -- coordinatewise neighbourhoods
  rw [nhds_pi, Filter.mem_pi] at hWn
  obtain ⟨I, -, s, hs, hsW⟩ := hWn
  have hsn : (⋂ j, s j) ∈ 𝓝 (0 : FiniteAdeles F) := Filter.iInter_mem.mpr fun j => hs j
  obtain ⟨N, hN, hNs⟩ := exists_nat_mul_mem_of_mem_nhds_zero F hsn
  refine ⟨N, hN, fun x u hu => hinv x u (hsW fun j _ => ?_)⟩
  obtain ⟨c, hc, hcu⟩ := hu j
  rw [hcu]
  exact Set.mem_iInter.mp (hNs c hc) j

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
