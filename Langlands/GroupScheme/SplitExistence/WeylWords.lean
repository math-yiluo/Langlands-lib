import Langlands.GroupScheme.SplitExistence.IntegralBase

/-!
# Weyl words and the minimal-height argument

For a root datum `P` with base `b`, a word `[i₁, …, i_m]` of simple roots defines the Weyl group
element `s_{i₁} ∘ ⋯ ∘ s_{i_m}` (`weylWord`). For a reduced root datum with finitely many roots,
every root is the image of a simple root under such a word (`exists_weylWord_root`).

The minimal-height argument (`mem_range_root_of_weylStable`): a set `Λ` of nonzero vectors that
is stable under the simple reflections, consists of nonnegative or nonpositive integral
combinations of the simple roots, and contains a multiple `k • α_i` of a simple root only for
`k = ± 1`, consists of roots.
-/

noncomputable section

namespace Langlands.GroupScheme.SplitExistence

open RootPairing Set

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : RootDatum J X Y) (b : P.Base)

/-- The Weyl group element `s_{i₁} ∘ ⋯ ∘ s_{i_m}` of a word `[i₁, …, i_m]` of simple roots. -/
def weylWord : List b.support → (X ≃ₗ[ℤ] X)
  | [] => LinearEquiv.refl ℤ X
  | i :: w => (weylWord w).trans (P.reflection i)

variable {P b}

@[simp]
theorem weylWord_nil (x : X) : weylWord P b [] x = x :=
  rfl

@[simp]
theorem weylWord_cons (i : b.support) (w : List b.support) (x : X) :
    weylWord P b (i :: w) x = P.reflection i (weylWord P b w x) :=
  rfl

theorem weylWord_cons_symm (i : b.support) (w : List b.support) (x : X) :
    (weylWord P b (i :: w)).symm x = (weylWord P b w).symm (P.reflection i x) :=
  rfl

theorem weylWord_append_singleton (w : List b.support) (i : b.support) (x : X) :
    weylWord P b (w ++ [i]) x = weylWord P b w (P.reflection i x) := by
  induction w generalizing x with
  | nil => rfl
  | cons j w ih => rw [List.cons_append, weylWord_cons, ih, weylWord_cons]

/-- Every root is the image of a simple root under a Weyl word. -/
theorem exists_weylWord_root [Finite J] [P.IsReduced] (j : J) :
    ∃ (w : List b.support) (i : b.support), P.root j = weylWord P b w (P.root i) := by
  refine b.induction_reflect
    (p := fun j => ∃ (w : List b.support) (i : b.support), P.root j = weylWord P b w (P.root i))
    j ?_ ?_ ?_
  · rintro k ⟨w, i, h⟩
    refine ⟨w ++ [i], i, ?_⟩
    rw [weylWord_append_singleton, reflection_apply_self, map_neg, ← h, root_reflectionPerm,
      reflection_apply_self]
  · intro k hk
    exact ⟨[], ⟨k, hk⟩, rfl⟩
  · rintro k l ⟨w, i, h⟩ hl
    exact ⟨⟨l, hl⟩ :: w, i, by rw [root_reflectionPerm, h, weylWord_cons]⟩

/-- The coefficients of an integral combination of the simple roots are unique. -/
theorem coeff_eq_of_sum_eq {c d : b.support → ℤ}
    (h : ∑ i, c i • P.root i = ∑ i, d i • P.root i) : c = d :=
  funext (Fintype.linearIndependent_iffₛ.mp b.linearIndepOn_root c d h)

/-- `Σ_t (k δ_{t,i}) α_t = k α_i`. -/
theorem sum_ite_smul_root [DecidableEq J] (i : b.support) (k : ℤ) :
    ∑ t : b.support, (if t = i then k else 0) • P.root t = k • P.root i := by
  simp [ite_smul]

private theorem rootForm_sum_eq [Fintype J] (μ : X) (c : b.support → ℕ) :
    P.RootForm μ (∑ i, c i • P.root i) = ∑ i, (c i : ℤ) * P.RootForm μ (P.root i) := by
  simp [map_sum, map_nsmul]

private theorem sum_mem_rootSpan (c : b.support → ℕ) :
    ∑ i, c i • P.root i ∈ P.rootSpan ℤ :=
  Submodule.sum_mem _ fun _ _ =>
    Submodule.smul_of_tower_mem _ _ (Submodule.subset_span (mem_range_self _))

variable {Λ : Set X}

/-- The minimal-height argument for nonnegative combinations of the simple roots. -/
private theorem mem_range_root_of_weylStable_pos [Finite J]
    (hW : ∀ i ∈ b.support, ∀ μ ∈ Λ, P.reflection i μ ∈ Λ)
    (hsign : ∀ μ ∈ Λ, ∃ c : b.support → ℕ,
      μ = ∑ i, c i • P.root i ∨ μ = -∑ i, c i • P.root i)
    (h0 : (0 : X) ∉ Λ)
    (hmul : ∀ i ∈ b.support, ∀ k : ℤ, k • P.root i ∈ Λ → k = 1 ∨ k = -1) :
    ∀ (N : ℕ) (c : b.support → ℕ), ∑ i, c i = N → ∑ i, c i • P.root i ∈ Λ →
      ∑ i, c i • P.root i ∈ range P.root := by
  classical
  have := Fintype.ofFinite J
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro c hN hμ
  generalize hμdef : ∑ i, c i • P.root i = μ at hμ ⊢
  have hμ0 : μ ≠ 0 := fun h => h0 (h ▸ hμ)
  have hpos := P.rootForm_pos_of_ne_zero (hμdef ▸ sum_mem_rootSpan c) hμ0
  have hexp := rootForm_sum_eq (P := P) μ c
  rw [hμdef] at hexp
  rw [hexp] at hpos
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℤ)) (by simpa using hpos)
  have hci : 0 < (c i : ℤ) := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hi with h | h
    · exact h.1
    · exact absurd h.1 (not_lt.2 (Int.natCast_nonneg _))
  have hBi : 0 < P.RootForm μ (P.root i) := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hi with h | h
    · exact h.2
    · exact absurd h.1 (not_lt.2 (Int.natCast_nonneg _))
  set p := P.toLinearMap μ (P.coroot i) with hp
  have hp0 : 0 < p := by
    have h2 := two_mul_rootForm_root P μ i
    have h4 := four_le_rootForm_root P i
    rw [← hp] at h2
    nlinarith
  have hrefl : P.reflection i μ = μ - p • P.root i := rfl
  by_cases hrest : ∀ t : b.support, t ≠ i → c t = 0
  · -- `μ` is a multiple of the simple root `α_i`
    have hμi : μ = (c i : ℤ) • P.root i := by
      rw [← hμdef, Finset.sum_eq_single i (fun t _ ht => by rw [hrest t ht, zero_smul])
        (by simp), natCast_zsmul]
    rw [hμi] at hμ
    rcases hmul i i.2 _ hμ with h | h
    · rw [hμi, h, one_smul]
      exact mem_range_self _
    · omega
  · push Not at hrest
    obtain ⟨t, hti, hct⟩ := hrest
    have hsμ := hW i i.2 μ hμ
    -- the coefficients of `s_i μ`
    have hcoef : P.reflection i μ =
        ∑ k : b.support, ((c k : ℤ) - if k = i then p else 0) • P.root k := by
      rw [hrefl, ← hμdef]
      simp only [sub_smul, Finset.sum_sub_distrib, sum_ite_smul_root, natCast_zsmul]
    obtain ⟨d, hd | hd⟩ := hsign _ hsμ
    · have hcd : (fun k => (c k : ℤ) - if k = i then p else 0) = fun k => (d k : ℤ) := by
        apply coeff_eq_of_sum_eq
        rw [← hcoef, hd]
        simp only [natCast_zsmul]
      have hdi := congrFun hcd i
      have hdk : ∀ k, k ≠ i → (d k : ℤ) = c k := fun k hk => by
        have := congrFun hcd k
        simp only [hk, ite_false, sub_zero] at this
        exact this.symm
      simp only [ite_true] at hdi
      have hsum : ((∑ k, d k : ℕ) : ℤ) = (N : ℤ) - p := by
        rw [← hN]
        push_cast
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
          Finset.sum_congr rfl fun k hk => hdk k (Finset.ne_of_mem_erase hk), ← hdi]
        ring
      have hlt : ∑ k, d k < N := by omega
      have hmem := ih _ hlt d rfl (by rw [← hd]; exact hsμ)
      rw [← hd] at hmem
      obtain ⟨j, hj⟩ := hmem
      refine ⟨P.reflectionPerm i j, ?_⟩
      rw [root_reflectionPerm, hj, reflection_same]
    · exfalso
      have hcd : (fun k => (c k : ℤ) - if k = i then p else 0) = fun k => -(d k : ℤ) := by
        apply coeff_eq_of_sum_eq
        rw [← hcoef, hd]
        simp only [neg_smul, Finset.sum_neg_distrib, natCast_zsmul]
      have := congrFun hcd t
      simp only [hti, ite_false, sub_zero] at this
      have hd0 : (0 : ℤ) ≤ d t := Int.natCast_nonneg _
      omega

/-- **The minimal-height argument.** A set `Λ` of nonzero vectors that is stable under the
simple reflections, consists of nonnegative or nonpositive integral combinations of the simple
roots, and contains a multiple `k • α_i` of a simple root only for `k = ± 1`, consists of roots. -/
theorem mem_range_root_of_weylStable [Finite J]
    (hW : ∀ i ∈ b.support, ∀ μ ∈ Λ, P.reflection i μ ∈ Λ)
    (hsign : ∀ μ ∈ Λ, ∃ c : b.support → ℕ,
      μ = ∑ i, c i • P.root i ∨ μ = -∑ i, c i • P.root i)
    (h0 : (0 : X) ∉ Λ)
    (hmul : ∀ i ∈ b.support, ∀ k : ℤ, k • P.root i ∈ Λ → k = 1 ∨ k = -1) :
    ∀ μ ∈ Λ, μ ∈ range P.root := by
  intro μ hμ
  obtain ⟨c, hc | hc⟩ := hsign μ hμ
  · subst hc
    exact mem_range_root_of_weylStable_pos hW hsign h0 hmul _ c rfl hμ
  · -- apply the positive case to `-Λ`
    have key := mem_range_root_of_weylStable_pos (P := P) (b := b) (Λ := {x | -x ∈ Λ})
      (fun i hi x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [← map_neg]
        exact hW i hi _ hx)
      (fun x hx => by
        obtain ⟨d, hd | hd⟩ := hsign _ hx
        · exact ⟨d, Or.inr (by rw [← hd, neg_neg])⟩
        · exact ⟨d, Or.inl (by rw [← neg_neg x, hd, neg_neg])⟩)
      (by simpa using h0)
      (fun i hi k hk => by
        simp only [Set.mem_ofPred_eq, ← neg_smul] at hk
        rcases hmul i hi _ hk with h | h <;> omega)
      _ c rfl (by show -(∑ i, c i • P.root i) ∈ Λ; rw [← hc]; exact hμ)
    obtain ⟨j, hj⟩ := key
    refine ⟨P.reflectionPerm j j, ?_⟩
    rw [root_reflectionPerm, reflection_apply_self, hj, hc]

end Langlands.GroupScheme.SplitExistence
