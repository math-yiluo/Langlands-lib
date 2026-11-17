import Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator

/-! # Closed root sets without opposite roots lie in a positive system -/

noncomputable section

namespace Langlands.LinearAlgebra

open Module

section Gordan

/-- A positive integer family can be made to dominate any other integer family after scaling. -/
theorem exists_mul_add_pos {k : ℕ} (p q : Fin k → ℤ) (hp : ∀ j, 0 < p j) :
    ∃ N : ℤ, ∀ j, 0 < N * p j + q j := by
  refine ⟨∑ j, |q j| + 1, fun j => ?_⟩
  have h1 : |q j| ≤ ∑ j, |q j| :=
    Finset.single_le_sum (f := fun j => |q j|) (fun j _ => abs_nonneg (q j))
      (Finset.mem_univ j)
  have h2 := neg_abs_le (q j)
  have h3 : 1 ≤ p j := hp j
  have h4 : 0 ≤ ∑ j, |q j| := Finset.sum_nonneg fun j _ => abs_nonneg (q j)
  nlinarith

/-- **Gordan's alternative over `ℤ`.** For a finite family of vectors in `ℤ^I`, either some
integral functional is positive on every member, or some nontrivial family of natural
coefficients gives the zero combination. -/
theorem gordan_int {I : Type*} [Fintype I] [DecidableEq I] :
    ∀ (k : ℕ) (v : Fin k → (I → ℤ)),
      (∃ f : Dual ℤ (I → ℤ), ∀ j, 0 < f (v j)) ∨
        (∃ c : Fin k → ℕ, c ≠ 0 ∧ ∑ j, c j • v j = 0) := by
  intro k
  induction k with
  | zero => exact fun v => Or.inl ⟨0, fun j => j.elim0⟩
  | succ k ih =>
    intro v
    let v' : Fin k → (I → ℤ) := fun j => v (Fin.castSucc j)
    let x : I → ℤ := v (Fin.last k)
    rcases ih v' with ⟨f, hf⟩ | ⟨c, hc0, hc⟩
    · rcases lt_trichotomy (f x) 0 with hneg | hzero | hpos
      · -- the new vector has negative value: project the family along it
        let a : ℤ := -f x
        have ha : 0 < a := by simp only [a]; omega
        let w : Fin k → (I → ℤ) := fun j => a • v' j + f (v' j) • x
        rcases ih w with ⟨g, hg⟩ | ⟨c, hc0, hc⟩
        · let z0 : Dual ℤ (I → ℤ) := a • g + g x • f
          have hz0x : z0 x = 0 := by
            simp only [z0, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, a]
            ring
          have hz0 : ∀ j, 0 < z0 (v' j) := by
            intro j
            have := hg j
            simp only [w, map_add, map_smul, smul_eq_mul] at this
            simp only [z0, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            linarith
          obtain ⟨N, hN⟩ := exists_mul_add_pos (fun j => z0 (v' j)) (fun j => -f (v' j)) hz0
          refine Or.inl ⟨N • z0 - f, fun j => ?_⟩
          refine Fin.lastCases ?_ (fun j => ?_) j
          · change 0 < (N • z0 - f) x
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, hz0x, smul_zero, zero_sub]
            omega
          · have := hN j
            change 0 < (N • z0 - f) (v' j)
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
            linarith
        · refine Or.inr ⟨Fin.lastCases (∑ j, c j * (f (v' j)).toNat)
            (fun j => c j * a.toNat), ?_, ?_⟩
          · obtain ⟨j, hj⟩ := Function.ne_iff.mp hc0
            refine Function.ne_iff.mpr ⟨Fin.castSucc j, ?_⟩
            simp only [Fin.lastCases_castSucc, Pi.zero_apply]
            have : 0 < a.toNat := by omega
            exact Nat.mul_ne_zero hj this.ne'
          · rw [Fin.sum_univ_castSucc]
            simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
            have hc' : ∑ j, ((c j : ℤ) • w j) = 0 := by
              simpa only [natCast_zsmul] using hc
            rw [← hc']
            simp only [← natCast_zsmul, w, smul_add, Finset.sum_add_distrib,
              Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg (hf _).le, mul_smul, Finset.sum_smul,
              x]
            congr 1
      · by_cases hx : x = 0
        · refine Or.inr ⟨Pi.single (Fin.last k) 1, ?_, ?_⟩
          · intro h
            have := congrFun h (Fin.last k)
            simp at this
          · rw [Finset.sum_eq_single (Fin.last k)]
            · simpa using hx
            · intro j _ hj
              simp [hj]
            · simp
        · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
          let g : Dual ℤ (I → ℤ) := x i • LinearMap.proj i
          have hgx : 0 < g x := by
            simp only [g, LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, smul_eq_mul]
            exact mul_self_pos.mpr hi
          obtain ⟨N, hN⟩ := exists_mul_add_pos (fun j => f (v' j)) (fun j => g (v' j)) hf
          refine Or.inl ⟨N • f + g, fun j => ?_⟩
          refine Fin.lastCases ?_ (fun j => ?_) j
          · change 0 < (N • f + g) x
            simp only [LinearMap.add_apply, LinearMap.smul_apply, hzero, smul_zero, zero_add]
            exact hgx
          · exact hN j
      · refine Or.inl ⟨f, fun j => ?_⟩
        refine Fin.lastCases ?_ (fun j => ?_) j
        · exact hpos
        · exact hf j
    · refine Or.inr ⟨Fin.lastCases 0 c, ?_, ?_⟩
      · obtain ⟨j, hj⟩ := Function.ne_iff.mp hc0
        refine Function.ne_iff.mpr ⟨Fin.castSucc j, ?_⟩
        simpa using hj
      · rw [Fin.sum_univ_castSucc]
        simpa using hc

end Gordan

section ClosedSets

variable {J X Y : Type*} [Finite J] [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y)

/-- **Integral saturation of closed root sets over `ℤ`.** A root which is a finite sum of members
of an additively closed set of roots belongs to that set. This is the integral version of
`RootPairing.IsAdditivelyClosedRootSet.multiset_sum_mem`. -/
theorem multiset_sum_mem_of_closed {S : Set X} (hS : S ⊆ Set.range P.root)
    (hcl : ∀ α ∈ S, ∀ β ∈ S, α + β ∈ Set.range P.root → α + β ∈ S)
    (s : Multiset X) (hs : ∀ α ∈ s, α ∈ S) (hroot : s.sum ∈ Set.range P.root) :
    s.sum ∈ S := by
  classical
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    obtain ⟨i, hi⟩ := hroot
    have hsum : (s.map (P.coroot' i)).sum = 2 := by
      rw [← map_multiset_sum, ← hi, RootPairing.root_coroot'_eq_pairing,
        RootPairing.pairing_same]
    have hpos : ∃ α ∈ s, 0 < P.coroot' i α := by
      by_contra! h
      have hle := Multiset.sum_map_le_sum_map (P.coroot' i) (fun _ : X => (0 : ℤ)) h
      have : (s.map (P.coroot' i)).sum ≤ 0 := by simpa using hle
      omega
    obtain ⟨α, hα, hαpos⟩ := hpos
    obtain ⟨j, hj⟩ := hS (hs α hα)
    by_cases hij : j = i
    · rw [← hi, ← hij, hj]
      exact hs α hα
    have hpair : 0 < P.pairingIn ℤ j i := by
      have hp : 0 < P.pairing j i := by
        simpa only [← hj, RootPairing.root_coroot'_eq_pairing] using hαpos
      rw [← P.algebraMap_pairingIn ℤ] at hp
      simpa using hp
    have hdiff : s.sum - α ∈ Set.range P.root := by
      rw [← hi, ← hj, ← neg_sub, RootPairing.neg_mem_range_root_iff]
      exact P.root_sub_root_mem_of_pairingIn_pos hpair hij
    have heq : (s.erase α).sum = s.sum - α := by
      have ht := congrArg Multiset.sum (Multiset.cons_erase hα)
      apply eq_sub_of_add_eq'
      simpa only [Multiset.sum_cons] using ht
    have htail : (s.erase α).sum ∈ S :=
      ih (s.erase α) (Multiset.erase_lt.mpr hα)
        (fun β hβ => hs β (Multiset.mem_of_mem_erase hβ)) (heq.symm ▸ hdiff)
    have ht := hcl α (hs α hα) (s.sum - α) (heq ▸ htail)
      (by simpa only [add_sub_cancel] using (show s.sum ∈ Set.range P.root from ⟨i, hi⟩))
    simpa only [add_sub_cancel] using ht

/-- In a closed set of roots containing no pair of opposite roots, no nonempty family of members
sums to zero. -/
theorem multiset_sum_ne_zero_of_closed (Ψ : Set J)
    (hcl : ∀ a ∈ Ψ, ∀ c ∈ Ψ, ∀ d : J, P.root d = P.root a + P.root c → d ∈ Ψ)
    (hopp : ∀ a ∈ Ψ, ∀ c ∈ Ψ, P.root a + P.root c ≠ 0)
    (s : Multiset X) (hs : ∀ α ∈ s, α ∈ P.root '' Ψ) (hne : s ≠ 0) : s.sum ≠ 0 := by
  classical
  let := P.indexNeg
  intro hzero
  obtain ⟨α, hα⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨a, ha, rfl⟩ := hs α hα
  have heq : (s.erase (P.root a)).sum = -P.root a := by
    have ht := congrArg Multiset.sum (Multiset.cons_erase hα)
    rw [Multiset.sum_cons, hzero] at ht
    exact eq_neg_of_add_eq_zero_right ht
  have hS : P.root '' Ψ ⊆ Set.range P.root := Set.image_subset_range _ _
  have hclS : ∀ α ∈ P.root '' Ψ, ∀ β ∈ P.root '' Ψ, α + β ∈ Set.range P.root →
      α + β ∈ P.root '' Ψ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ ⟨d, hd⟩
    exact ⟨d, hcl a ha c hc d hd, hd⟩
  have hmem := multiset_sum_mem_of_closed P hS hclS (s.erase (P.root a))
    (fun β hβ => hs β (Multiset.mem_of_mem_erase hβ))
    (by rw [heq]; exact ⟨-a, by simp⟩)
  rw [heq] at hmem
  obtain ⟨c, hc, hc'⟩ := hmem
  exact hopp a ha c hc (by rw [hc']; abel)

/-- A closed set of roots contains every root of the form `p a + q c` with `a`, `c` in the set
and natural coefficients `p`, `q`. -/
theorem mem_of_root_eq_nsmul_add_nsmul (Ψ : Set J)
    (hcl : ∀ a ∈ Ψ, ∀ c ∈ Ψ, ∀ d : J, P.root d = P.root a + P.root c → d ∈ Ψ)
    {a c d : J} (ha : a ∈ Ψ) (hc : c ∈ Ψ) (p q : ℕ)
    (h : P.root d = p • P.root a + q • P.root c) : d ∈ Ψ := by
  classical
  have hS : P.root '' Ψ ⊆ Set.range P.root := Set.image_subset_range _ _
  have hclS : ∀ α ∈ P.root '' Ψ, ∀ β ∈ P.root '' Ψ, α + β ∈ Set.range P.root →
      α + β ∈ P.root '' Ψ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ ⟨d, hd⟩
    exact ⟨d, hcl a ha c hc d hd, hd⟩
  let s : Multiset X := Multiset.replicate p (P.root a) + Multiset.replicate q (P.root c)
  have hsum : s.sum = P.root d := by
    simp only [s, Multiset.sum_add, Multiset.sum_replicate, h]
  have hs : ∀ α ∈ s, α ∈ P.root '' Ψ := by
    intro α hα
    rcases Multiset.mem_add.mp hα with hα | hα
    · rw [Multiset.eq_of_mem_replicate hα]
      exact ⟨a, ha, rfl⟩
    · rw [Multiset.eq_of_mem_replicate hα]
      exact ⟨c, hc, rfl⟩
  have hmem := multiset_sum_mem_of_closed P hS hclS s hs (by rw [hsum]; exact ⟨d, rfl⟩)
  rw [hsum] at hmem
  obtain ⟨d', hd', hdd⟩ := hmem
  rwa [← P.root.injective hdd]

end ClosedSets

section Base

variable {J I : Type*} [Finite J] [Fintype I] (P : RootDatum J (I → ℤ) (I → ℤ))

/-- **Closed root sets without opposite pairs are positive for some base** (Bourbaki, *Lie groups
and Lie algebras*, Ch. VI, §1.7, Prop. 22; Conrad, *Reductive group schemes*, Lemma 5.1.15). -/
theorem exists_base_isPos_of_closed [P.IsReduced] (Ψ : Set J)
    (hcl : ∀ a ∈ Ψ, ∀ c ∈ Ψ, ∀ d : J, P.root d = P.root a + P.root c → d ∈ Ψ)
    (hopp : ∀ a ∈ Ψ, ∀ c ∈ Ψ, P.root a + P.root c ≠ 0) :
    ∃ b : P.Base, ∀ a ∈ Ψ, b.IsPos a := by
  classical
  have := Fintype.ofFinite J
  let e := (Finite.equivFin Ψ).symm
  rcases gordan_int (Nat.card Ψ) (fun j => P.root (e j : J)) with ⟨f, hf⟩ | ⟨c, hc0, hc⟩
  · let g : Dual ℤ (I → ℤ) := f ∘ₗ P.flip.Polarization
    obtain ⟨b, hb⟩ := exists_base_isPos_of_pos P g
    refine ⟨b, fun a ha => hb a ?_⟩
    have h := (Langlands.GroupScheme.SplitExistence.dual_polarization_root_pos_iff P.flip f a).mpr
    obtain ⟨j, hj⟩ := e.surjective ⟨a, ha⟩
    have := hf j
    rw [hj] at this
    exact h this
  · exfalso
    let s : Multiset (I → ℤ) :=
      Finset.univ.val.bind fun j => Multiset.replicate (c j) (P.root (e j : J))
    have hsum : s.sum = ∑ j, c j • P.root (e j : J) := by
      rw [Multiset.sum_bind]
      simp only [Multiset.sum_replicate]
      rfl
    refine multiset_sum_ne_zero_of_closed P Ψ hcl hopp s ?_ ?_ (hsum.trans hc)
    · intro α hα
      obtain ⟨j, -, hj⟩ := Multiset.mem_bind.mp hα
      rw [Multiset.eq_of_mem_replicate hj]
      exact ⟨e j, (e j).2, rfl⟩
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp hc0
      intro hs
      have : Multiset.replicate (c j) (P.root (e j : J)) ≤ s :=
        Multiset.le_bind _ (Finset.mem_univ_val j)
      have h0 := congrArg Multiset.card (Multiset.le_zero.mp (hs ▸ this))
      simp only [Multiset.card_replicate, Multiset.card_zero] at h0
      exact hj h0

end Base

end Langlands.LinearAlgebra
