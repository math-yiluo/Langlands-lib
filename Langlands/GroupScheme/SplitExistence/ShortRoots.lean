import Langlands.GroupScheme.SplitExistence.StringRep
import Langlands.GroupScheme.SplitExistence.MinimalWeights
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Short roots, strings of length at most one, and a positive functional

A root `α_j` of a root datum is *short* (`IsShortRoot`) when `|⟨α_j, α_k^∨⟩| ≤ 1` for every root
`α_k ≠ ±α_j`. Short roots are permuted by the reflections, and every root `α_x` that is not
short has a short root `β` with `⟨β, α_x^∨⟩ = -1` (`exists_isShortRoot_pairing_eq_neg_one`).

A family of weights with pairings in `[-1, 1]` against `α^∨` that is stable under the
reflection along `α` has root-string data with strings of length at most one
(`StringData.ofUnit`); a family of weights orthogonal to `α^∨` has the string decomposition into
strings of length zero (`StringDecomp.trivial`).

Finally, the sum `⟨·, 2ρ^∨⟩` of the pairings with the positive coroots takes the value `2` on
every simple root (`posCorootSum_root`).
-/

noncomputable section

universe u

open RootPairing

namespace Langlands.GroupScheme.SplitExistence

/-! ### Strings of length at most one -/

section Strings

variable {X : Type*} [AddCommGroup X] {α : X} {pair : X →+ ℤ}

/-- Root-string data for a family of weights whose pairings with `α^∨` lie in `[-1, 1]` and
which is stable under the reflection `μ ↦ μ - pair μ • α`: `bot d = 1` if `pair (ω d) = 1`,
`top d = 1` if `pair (ω d) = -1`, and both are zero otherwise. -/
def StringData.ofUnit {C : Type u} {ω : C → X} (hinj : Function.Injective ω) (hα : pair α = 2)
    (hp : ∀ d, |pair (ω d)| ≤ 1) (hs : ∀ d, ∃ d', ω d' = ω d - pair (ω d) • α) :
    StringData α pair C ω where
  bot d := if pair (ω d) = 1 then 1 else 0
  top d := if pair (ω d) = -1 then 1 else 0
  injective := hinj
  exists_iff d z := by
    constructor
    · rintro ⟨d', hd'⟩
      have h1 := congrArg pair hd'
      rw [map_add, map_zsmul, hα, smul_eq_mul] at h1
      have h2 := abs_le.1 (hp d)
      have h3 := abs_le.1 (hp d')
      split_ifs <;> push_cast <;> omega
    · rintro ⟨h1, h2⟩
      have h3 := abs_le.1 (hp d)
      have hz : z = 0 ∨ (z = 1 ∧ pair (ω d) = -1) ∨ (z = -1 ∧ pair (ω d) = 1) := by
        split_ifs at h1 h2 <;> push_cast at h1 h2 <;> omega
      rcases hz with rfl | ⟨rfl, hpd⟩ | ⟨rfl, hpd⟩
      · exact ⟨d, by simp⟩
      · obtain ⟨d', hd'⟩ := hs d
        exact ⟨d', by rw [hd', hpd]; module⟩
      · obtain ⟨d', hd'⟩ := hs d
        exact ⟨d', by rw [hd', hpd]; module⟩
  bot_add_top_le d := by split_ifs <;> omega
  pair_eq d := by
    have h := abs_le.1 (hp d)
    split_ifs <;> push_cast <;> omega

theorem StringData.ofUnit_bot {C : Type u} {ω : C → X} (hinj : Function.Injective ω)
    (hα : pair α = 2) (hp : ∀ d, |pair (ω d)| ≤ 1) (hs : ∀ d, ∃ d', ω d' = ω d - pair (ω d) • α)
    (d : C) : (StringData.ofUnit hinj hα hp hs).bot d = if pair (ω d) = 1 then 1 else 0 := rfl

theorem StringData.ofUnit_top {C : Type u} {ω : C → X} (hinj : Function.Injective ω)
    (hα : pair α = 2) (hp : ∀ d, |pair (ω d)| ≤ 1) (hs : ∀ d, ∃ d', ω d' = ω d - pair (ω d) • α)
    (d : C) : (StringData.ofUnit hinj hα hp hs).top d = if pair (ω d) = -1 then 1 else 0 := rfl

open Classical in
/-- The raising operator of the string decomposition of a family as in `StringData.ofUnit`
moves `ω c` to `ω c + α` with coefficient one. -/
theorem StringData.ofUnit_decomp_E_one {C : Type u} [Finite C] {ω : C → X}
    (hinj : Function.Injective ω) (hα : pair α = 2) (hp : ∀ d, |pair (ω d)| ≤ 1)
    (hs : ∀ d, ∃ d', ω d' = ω d - pair (ω d) • α) (r c : C) :
    (StringData.ofUnit hinj hα hp hs).decomp.E 1 r c = if ω r = ω c + α then 1 else 0 := by
  rw [StringData.decomp_E_one]
  by_cases hc : ω r = ω c + α
  · simp only [hc, ↓reduceIte]
    have h := ((StringData.ofUnit hinj hα hp hs).exists_iff r (-1)).1 ⟨c, by rw [hc]; module⟩
    rw [ofUnit_bot] at h ⊢
    by_cases hp1 : pair (ω r) = 1
    · simp [hp1]
    · simp [hp1] at h
  · simp only [hc, ↓reduceIte]

open Classical in
/-- The lowering operator of the string decomposition of a family as in `StringData.ofUnit`
moves `ω c` to `ω c - α` with coefficient one. -/
theorem StringData.ofUnit_decomp_F_one {C : Type u} [Finite C] {ω : C → X}
    (hinj : Function.Injective ω) (hα : pair α = 2) (hp : ∀ d, |pair (ω d)| ≤ 1)
    (hs : ∀ d, ∃ d', ω d' = ω d - pair (ω d) • α) (r c : C) :
    (StringData.ofUnit hinj hα hp hs).decomp.F 1 r c = if ω r + α = ω c then 1 else 0 := by
  rw [StringData.decomp_F_one]
  by_cases hc : ω r + α = ω c
  · simp only [hc, ↓reduceIte]
    have h := ((StringData.ofUnit hinj hα hp hs).exists_iff r 1).1 ⟨c, by rw [← hc]; module⟩
    rw [ofUnit_top] at h ⊢
    by_cases hp1 : pair (ω r) = -1
    · simp [hp1]
    · simp [hp1] at h
  · simp only [hc, ↓reduceIte]

/-- The string decomposition of a family of weights orthogonal to `α^∨` into strings of length
zero. -/
def StringDecomp.trivial {C : Type u} [Fintype C] [DecidableEq C] (ω : C → X)
    (h : ∀ d, pair (ω d) = 0) : StringDecomp α pair C ω where
  K := C
  len _ := 0
  len_le _ := Nat.zero_le _
  eqv :=
    { toFun := fun d => ⟨d, 0⟩
      invFun := fun x => x.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨k, j⟩
        have hj : j = 0 := Fin.ext (by have := j.isLt; rw [Fin.val_zero]; omega)
        subst hj
        rfl }
  weight_eq k j := by
    have hj : (j : ℕ) = 0 := by have := j.isLt; omega
    show ω k = ω k + (j : ℕ) • α
    rw [hj, zero_smul, add_zero]
  pair_bot k := by
    show pair (ω k) = _
    rw [h]
    simp

theorem StringDecomp.trivial_E_one {C : Type u} [Fintype C] [DecidableEq C] (ω : C → X)
    (h : ∀ d, pair (ω d) = 0) : (StringDecomp.trivial (α := α) ω h).E 1 = 0 := by
  ext r c
  rw [StringDecomp.E_apply]
  simp [StringDecomp.trivial]

theorem StringDecomp.trivial_F_one {C : Type u} [Fintype C] [DecidableEq C] (ω : C → X)
    (h : ∀ d, pair (ω d) = 0) : (StringDecomp.trivial (α := α) ω h).F 1 = 0 := by
  ext r c
  rw [StringDecomp.F_apply]
  simp [StringDecomp.trivial]

end Strings

/-! ### Short roots -/

section Short

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] (P : RootDatum J X Y)

/-- A root `α_j` is *short* when `|⟨α_j, α_k^∨⟩| ≤ 1` for every root `α_k ≠ ±α_j`. -/
def IsShortRoot (j : J) : Prop :=
  ∀ k, P.root k ≠ P.root j → P.root k ≠ -P.root j → |P.pairing j k| ≤ 1

variable {P}

theorem root_reflectionPerm_self (i : J) : P.root (P.reflectionPerm i i) = -P.root i := by
  rw [root_reflectionPerm, reflection_apply_self]

/-- The pairing of a reflected root: `⟨s_i α_j, α_k^∨⟩ = ⟨α_j, α_k^∨⟩ - ⟨α_j, α_i^∨⟩ ⟨α_i, α_k^∨⟩`. -/
theorem pairing_reflectionPerm_left (i j k : J) :
    P.pairing (P.reflectionPerm i j) k = P.pairing j k - P.pairing j i * P.pairing i k := by
  simp only [← root_coroot_eq_pairing, root_reflectionPerm, reflection_apply_root, map_sub,
    map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]

theorem IsShortRoot.reflectionPerm {j : J} (hj : IsShortRoot P j) (i : J) :
    IsShortRoot P (P.reflectionPerm i j) := by
  intro k hk hk'
  rw [← pairing_reflectionPerm]
  apply hj
  · intro h
    apply hk
    rw [← P.root.injective h, reflectionPerm_self]
  · intro h
    apply hk'
    have h' := congrArg (P.reflection i) h
    rw [← root_reflectionPerm, reflectionPerm_self, map_neg, ← root_reflectionPerm] at h'
    exact h'

theorem IsShortRoot.abs_pairing_le_one {j : J} (hj : IsShortRoot P j) {k : J}
    (hk : P.root k ≠ P.root j) (hk' : P.root k ≠ -P.root j) :
    P.pairing j k = -1 ∨ P.pairing j k = 0 ∨ P.pairing j k = 1 := by
  have := abs_le.1 (hj k hk hk')
  omega

/-- A root equal to `±` a short root is short. -/
theorem IsShortRoot.of_root_eq {j k : J} (hj : IsShortRoot P j)
    (h : P.root k = P.root j ∨ P.root k = -P.root j) : IsShortRoot P k := by
  rcases h with h | h
  · rw [P.root.injective h]
    exact hj
  · have : k = P.reflectionPerm j j := P.root.injective (by rw [h, root_reflectionPerm_self])
    rw [this]
    exact hj.reflectionPerm j

theorem pairingIn_int (i j : J) : P.pairingIn ℤ i j = P.pairing i j := by
  have := P.algebraMap_pairingIn ℤ i j
  rwa [Algebra.algebraMap_self_apply] at this

/-- The two pairings of two roots that are not proportional. -/
theorem pairing_pairing_mem [Finite J] [P.IsReduced] {i j : J} (h1 : P.root i ≠ P.root j)
    (h2 : P.root i ≠ -P.root j) :
    (P.pairing i j, P.pairing j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1)} : Set (ℤ × ℤ)) := by
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i j h1 h2
  rwa [pairingIn_int, pairingIn_int] at this

/-- Twice a root is not a root, in a reduced root datum. -/
theorem root_ne_two_smul [P.IsReduced] (i k : J) : P.root k ≠ (2 : ℤ) • P.root i := by
  intro h
  have hdep : ¬ LinearIndependent ℤ ![P.root k, P.root i] := by
    rw [LinearIndependent.pair_iff]
    intro hli
    have := hli 1 (-2) (by rw [h]; module)
    simp at this
  rcases (RootPairing.IsReduced.eq_or_eq_neg (P := P) k i hdep) with h' | h'
  · have h1 := congrArg (fun x => P.toLinearMap x (P.coroot i)) (h.symm.trans h')
    simp only [map_zsmul, LinearMap.smul_apply, root_coroot_eq_pairing, pairing_same,
      smul_eq_mul] at h1
    omega
  · have h1 := congrArg (fun x => P.toLinearMap x (P.coroot i)) (h.symm.trans h')
    simp only [map_zsmul, map_neg, LinearMap.smul_apply, LinearMap.neg_apply,
      root_coroot_eq_pairing, pairing_same, smul_eq_mul] at h1
    omega

theorem root_ne_neg_two_smul [P.IsReduced] (i k : J) : P.root k ≠ -((2 : ℤ) • P.root i) := by
  intro h
  apply root_ne_two_smul (P := P) (P.reflectionPerm i i) k
  rw [h, root_reflectionPerm_self, smul_neg]

variable [Fintype J] [P.IsReduced]

/-- Every root that is not short has a short root `β` with `⟨β, α_x^∨⟩ = -1`. -/
theorem exists_isShortRoot_pairing_eq_neg_one (x : J) (hx : ¬ IsShortRoot P x) :
    ∃ β, IsShortRoot P β ∧ P.pairing β x = -1 := by
  suffices H : ∀ N : ℕ, ∀ x : J, P.RootForm (P.root x) (P.root x) ≤ N → ¬ IsShortRoot P x →
      ∃ β, IsShortRoot P β ∧ P.pairing β x = -1 from
    H _ x (Int.self_le_toNat _) hx
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x hxN hx
  have hx' := hx
  simp only [IsShortRoot, not_forall, not_le] at hx
  obtain ⟨k, hk1, hk2, hk⟩ := hx
  have hmem := pairing_pairing_mem (P := P) (i := x) (j := k) (Ne.symm hk1)
    (fun h => hk2 (by rw [h, neg_neg]))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rw [lt_abs] at hk
  have hnorm := two_mul_rootForm_root P (P.root x) k
  have hnorm' := two_mul_rootForm_root P (P.root k) x
  rw [root_coroot_eq_pairing] at hnorm hnorm'
  rw [rootForm_comm P (P.root k)] at hnorm'
  have h4 := four_le_rootForm_root P k
  have key : (P.pairing k x = 1 ∨ P.pairing k x = -1) ∧
      P.RootForm (P.root k) (P.root k) < P.RootForm (P.root x) (P.root x) := by
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1] at hnorm hk <;> rw [h2] at hnorm' ⊢ <;> omega
  -- the root `γ = ± α_k` with `⟨γ, α_x^∨⟩ = -1`
  obtain ⟨γ, hγx, hγnorm⟩ : ∃ γ : J, P.pairing γ x = -1 ∧
      P.RootForm (P.root γ) (P.root γ) = P.RootForm (P.root k) (P.root k) := by
    by_cases hkx : P.pairing k x = -1
    · exact ⟨k, hkx, rfl⟩
    · refine ⟨P.reflectionPerm k k, ?_, ?_⟩
      · rw [pairing_reflectionPerm_self_left]
        omega
      · rw [root_reflectionPerm_self]
        simp
  by_cases hγs : IsShortRoot P γ
  · exact ⟨γ, hγs, hγx⟩
  have hγN : (P.RootForm (P.root γ) (P.root γ)).toNat < N := by
    have := rootForm_self_nonneg P (P.root γ)
    omega
  obtain ⟨β', hβ's, hβ'γ⟩ := ih _ hγN γ (Int.self_le_toNat _) hγs
  have hβ'x1 : P.root x ≠ P.root β' := fun h => hx' (hβ's.of_root_eq (Or.inl h))
  have hβ'x2 : P.root x ≠ -P.root β' := fun h => hx' (hβ's.of_root_eq (Or.inr h))
  rcases hβ's.abs_pairing_le_one hβ'x1 hβ'x2 with h | h | h
  · exact ⟨β', hβ's, h⟩
  · refine ⟨P.reflectionPerm γ β', hβ's.reflectionPerm γ, ?_⟩
    rw [pairing_reflectionPerm_left, h, hβ'γ, hγx]
    norm_num
  · refine ⟨P.reflectionPerm β' β', hβ's.reflectionPerm β', ?_⟩
    rw [pairing_reflectionPerm_self_left, h]

end Short

/-! ### A functional positive on the simple roots -/

section Positive

variable {J X Y : Type u} [Fintype J] [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}
  [P.IsReduced] (b : P.Base)

open Classical in
/-- The sum `⟨·, 2ρ^∨⟩` of the pairings with the positive coroots. -/
def posCorootSum : X →+ ℤ where
  toFun x := ∑ j ∈ Finset.univ.filter b.IsPos, P.toLinearMap x (P.coroot j)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

/-- `⟨α_i, 2ρ^∨⟩ = 2` for every simple root `α_i`. -/
theorem posCorootSum_root {i : J} (hi : i ∈ b.support) : posCorootSum b (P.root i) = 2 := by
  classical
  have hpos : b.IsPos i := Base.isPos_of_mem_support hi
  have hmem : i ∈ Finset.univ.filter b.IsPos := by simp [hpos]
  show ∑ j ∈ Finset.univ.filter b.IsPos, P.toLinearMap (P.root i) (P.coroot j) = 2
  rw [← Finset.add_sum_erase _ _ hmem, root_coroot_eq_pairing, pairing_same]
  simp only [root_coroot_eq_pairing]
  have hsum : ∑ j ∈ (Finset.univ.filter b.IsPos).erase i, P.pairing i j = 0 := by
    have hinv : ∀ j, P.pairing i j + P.pairing i (P.reflectionPerm i j) = 0 := by
      intro j
      rw [pairing_reflectionPerm, pairing_reflectionPerm_self_left, add_neg_cancel]
    refine Finset.sum_involution (fun j _ => P.reflectionPerm i j) (fun j _ => hinv j) ?_ ?_ ?_
    · intro j _ hf heq
      apply hf
      have := hinv j
      rw [heq] at this
      omega
    · intro j hj
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨fun h => ?_, hj.2.reflectionPerm hi hj.1⟩
      have hj' : j = P.reflectionPerm i i := by
        have := congrArg (P.reflectionPerm i) h
        rwa [reflectionPerm_self] at this
      have := (Base.IsPos.neg_iff_not b i).1
      rw [hj'] at hj
      exact this hj.2 hpos
    · intro j _
      exact reflectionPerm_self P i j
  rw [hsum, add_zero]

theorem posCorootSum_pos {i : J} (hi : i ∈ b.support) : 0 < posCorootSum b (P.root i) := by
  rw [posCorootSum_root b hi]
  norm_num

end Positive

end Langlands.GroupScheme.SplitExistence
