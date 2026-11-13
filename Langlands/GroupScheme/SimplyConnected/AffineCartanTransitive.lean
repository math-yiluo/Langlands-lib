import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Reductive.DominantMultipleRootData

/-!
# Vertex-transitive affine extensions of Cartan matrices are of type `A`

Let `A` be an integer matrix on a finite type `ι` and let `B` be an extension of `A` to
`Option ι` (one extra vertex `none`) which is a generalized Cartan matrix having a positive
left kernel vector, and whose automorphism group acts transitively on `Option ι`. If no nonzero integer vector is killed by `A`, then `A` is the
Cartan matrix of type `A_n` with `n = card ι`, after renumbering `ι`.

The last section applies this to the actual Cartan pairings `d.cartan` of a Tits-index datum,
whose nondegeneracy follows from the Library's
`Langlands.RootDatum.DominantMultiple.cartan_det_ne_zero`.
-/

noncomputable section

universe u v

open Finset CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace AffineCartan

/-! ## Entries of the type-`A` Cartan matrix -/

lemma cartanA_symm (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n i j = CartanMatrix.A n j i := by
  simp only [CartanMatrix.A, Matrix.of_apply, eq_comm (a := i)]
  split_ifs <;> omega

lemma cartanA_castSucc (n : ℕ) (i j : Fin (n + 1)) :
    CartanMatrix.A (n + 2) i.castSucc j.castSucc = CartanMatrix.A (n + 1) i j := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.castSucc_inj, Fin.val_castSucc]

lemma cartanA_last_last (n : ℕ) :
    CartanMatrix.A (n + 1) (Fin.last n) (Fin.last n) = 2 := by
  simp [CartanMatrix.A]

lemma cartanA_last_castSucc (n : ℕ) (j : Fin (n + 1)) :
    CartanMatrix.A (n + 2) (Fin.last (n + 1)) j.castSucc = if j = Fin.last n then -1 else 0 := by
  have hj := j.isLt
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
  split_ifs <;> omega

lemma cartanA_rev (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n i.rev j.rev = CartanMatrix.A n i j := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_rev]
  split_ifs <;> omega

lemma cartanA_rowSum_eq_zero (n : ℕ) (i : Fin n) (h0 : 0 < i.val) (h1 : i.val + 1 < n) :
    ∑ j, CartanMatrix.A n i j = 0 := by
  have key : ∀ j : Fin n, CartanMatrix.A n i j =
      (if j = i then 2 else 0) + (if j = ⟨i.val - 1, by omega⟩ then -1 else 0) +
        (if j = ⟨i.val + 1, h1⟩ then -1 else 0) := by
    intro j
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  norm_num

/-! ## Path matrices -/

/-- A symmetric integer matrix with diagonal `2`, off-diagonal entries in `{0, -1}`,
nonnegative row sums adding up to `2`, and no nonempty closed set of vertices with zero
row sums, is the type-`A` Cartan matrix after renumbering. -/
theorem exists_equiv_cartanA_of_path (r : ℕ) :
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι = r + 1 →
    ∀ (A : Matrix ι ι ℤ), (∀ a, A a a = 2) → (∀ a b, a ≠ b → A a b = 0 ∨ A a b = -1) →
      (∀ a b, A a b = A b a) → (∀ a, 0 ≤ ∑ b, A a b) → ∑ a, ∑ b, A a b = 2 →
      (∀ T : Finset ι, (∀ a ∈ T, ∀ b, A a b ≠ 0 → b ∈ T) → (∀ a ∈ T, ∑ b, A a b = 0) →
        T = ∅) →
      ∃ e : ι ≃ Fin (r + 1), ∀ a b, A a b = CartanMatrix.A (r + 1) (e a) (e b) := by
  induction r with
  | zero =>
    intro ι _ _ hcard A hdiag _ _ _ _ _
    refine ⟨Fintype.equivFinOfCardEq hcard, fun a b => ?_⟩
    have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcard.le
    rw [Subsingleton.elim a b, hdiag]
    simp [CartanMatrix.A]
  | succ r ih =>
    intro ι _ _ hcard A hdiag hoff hsymm hnonneg hsum hclosed
    -- a vertex with positive row sum
    obtain ⟨a, ha⟩ : ∃ a, 0 < ∑ b, A a b := by
      by_contra! h
      have : ∑ a, ∑ b, A a b = 0 :=
        Finset.sum_eq_zero fun a _ => le_antisymm (h a) (hnonneg a)
      omega
    have hle : ∀ a b, a ≠ b → A a b ≤ 0 := fun a b h => by rcases hoff a b h with h | h <;> omega
    -- it has a neighbour
    obtain ⟨b, hba, hab⟩ : ∃ b, b ≠ a ∧ A a b = -1 := by
      by_contra! h
      have h0 : ∀ c, c ≠ a → A a c = 0 := fun c hc => by
        rcases hoff a c hc.symm with h' | h'
        · exact h'
        · exact absurd h' (h c hc)
      have hrowa : ∑ c, A a c = 2 := by
        rw [Fintype.sum_eq_add_sum_subtype_ne _ a, hdiag,
          Finset.sum_eq_zero fun x _ => h0 x.val x.prop, add_zero]
      have hrest : ∀ c ∈ univ.erase a, ∑ x, A c x = 0 := by
        have hsplit := Finset.add_sum_erase univ (fun c => ∑ x, A c x) (mem_univ a)
        rw [hsum, hrowa] at hsplit
        exact (Finset.sum_eq_zero_iff_of_nonneg (s := univ.erase a)
          (fun c _ => hnonneg c)).mp (by omega)
      have hT := hclosed (univ.erase a) (fun c hc x hx => by
        refine mem_erase.mpr ⟨fun hxa => ?_, mem_univ x⟩
        subst hxa
        exact hx (by rw [hsymm]; exact h0 c (ne_of_mem_erase hc))) hrest
      obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a
      have : c ∈ univ.erase a := mem_erase.mpr ⟨hc, mem_univ c⟩
      rw [hT] at this
      exact absurd this (Finset.notMem_empty c)
    -- it has no other neighbour
    have hab0 : ∀ c, c ≠ a → c ≠ b → A a c = 0 := by
      intro c hca hcb
      rcases hoff a c hca.symm with h | h
      · exact h
      exfalso
      have hbound : ∀ x, A a x ≤ (if x = a then 2 else 0) + (if x = b then -1 else 0) +
          (if x = c then -1 else 0) := by
        intro x
        by_cases hxa : x = a
        · subst hxa; simp [hdiag, hba.symm, hca.symm]
        by_cases hxb : x = b
        · subst hxb; simp [hab, hxa, hcb.symm]
        by_cases hxc : x = c
        · subst hxc; simp [h, hxa, hxb]
        simp [hxa, hxb, hxc, hle a x (Ne.symm hxa)]
      have := Finset.sum_le_sum fun x (_ : x ∈ univ) => hbound x
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, ite_true] at this
      omega
    have hrowa : ∀ x, A a x = (if x = a then 2 else 0) + (if x = b then -1 else 0) := by
      intro x
      by_cases hxa : x = a
      · subst hxa; simp [hdiag, hba.symm]
      by_cases hxb : x = b
      · subst hxb; simp [hab, hxa]
      simp [hxa, hxb, hab0 x hxa hxb]
    have hsa : ∑ x, A a x = 1 := by
      simp only [hrowa, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, ite_true]
      norm_num
    have hcola : ∑ x, A x a = 1 := by simpa only [hsymm _ a] using hsa
    -- delete `a`
    let ι' := {x : ι // x ≠ a}
    have hcard' : Fintype.card ι' = r + 1 := by
      have := Fintype.card_congr (Equiv.optionSubtypeNe a)
      rw [Fintype.card_option] at this
      show Fintype.card {x : ι // x ≠ a} = r + 1
      omega
    let A' : Matrix ι' ι' ℤ := fun x y => A x y
    have hsum' : ∀ x : ι', ∑ y, A' x y = ∑ y, A x y - A x a := by
      intro x
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun y => A x y) a]
      ring
    have hxa_le : ∀ x : ι', A x a ≤ 0 := fun x => hle _ _ x.prop
    obtain ⟨e', he'⟩ := ih (ι := ι') hcard' A' (fun x => hdiag x)
      (fun x y hxy => hoff x y (fun h => hxy (Subtype.ext h))) (fun x y => hsymm x y)
      (fun x => by rw [hsum']; linarith [hnonneg x.val, hxa_le x])
      (by
        simp only [hsum', Finset.sum_sub_distrib]
        have h1 : ∑ x, ∑ y, A x y = ∑ y, A a y + ∑ x : ι', ∑ y, A x.val y :=
          Fintype.sum_eq_add_sum_subtype_ne _ a
        have h2 : ∑ x, A x a = A a a + ∑ x : ι', A x.val a :=
          Fintype.sum_eq_add_sum_subtype_ne _ a
        rw [hsum, hsa] at h1
        rw [hcola, hdiag] at h2
        linarith)
      (by
        intro T' hT'cl hT'z
        have hbT : ∀ x ∈ T', x.val ≠ b := by
          intro x hx hxb
          have := hT'z x hx
          rw [hsum', hxb, hsymm b a, hab] at this
          linarith [hnonneg b]
        have hT := hclosed (T'.map (Function.Embedding.subtype _)) (by
            intro y hy c hc
            obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
            by_cases hca : c = a
            · subst hca
              exfalso
              have hxa : (x : ι) ≠ c := x.prop
              rw [hsymm] at hc
              exact hc (hab0 x hxa (hbT x hx))
            · exact Finset.mem_map.mpr ⟨⟨c, hca⟩, hT'cl x hx ⟨c, hca⟩ hc, rfl⟩)
          (by
            intro y hy
            obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
            have h1 := hT'z x hx
            rw [hsum'] at h1
            have h2 : A x a = 0 := by rw [hsymm]; exact hab0 x x.prop (hbT x hx)
            simp only [Function.Embedding.coe_subtype]
            linarith)
        simpa using hT)
    -- position of `b`
    let b' : ι' := ⟨b, hba⟩
    have hb'sum : 1 ≤ ∑ y, A' b' y := by
      rw [hsum']
      simp only [b']
      rw [hsymm b a, hab]
      linarith [hnonneg b]
    have hpos : (e' b').val = 0 ∨ (e' b').val = r := by
      by_contra! h
      have hrs : ∑ j, CartanMatrix.A (r + 1) (e' b') j = 0 :=
        cartanA_rowSum_eq_zero (r + 1) (e' b') (Nat.pos_of_ne_zero h.1)
          (by have := (e' b').isLt; omega)
      have : ∑ y, A' b' y = ∑ j, CartanMatrix.A (r + 1) (e' b') j := by
        rw [← Equiv.sum_comp e']
        exact Finset.sum_congr rfl fun y _ => he' b' y
      omega
    obtain ⟨e'', he''A, he''b⟩ : ∃ e'' : ι' ≃ Fin (r + 1),
        (∀ x y, A' x y = CartanMatrix.A (r + 1) (e'' x) (e'' y)) ∧ e'' b' = Fin.last r := by
      rcases hpos with h | h
      · refine ⟨e'.trans Fin.revPerm, fun x y => ?_, ?_⟩
        · simp only [Equiv.trans_apply, Fin.revPerm_apply, cartanA_rev]
          exact he' x y
        · simp only [Equiv.trans_apply, Fin.revPerm_apply]
          ext
          simp [Fin.val_rev, h]
      · exact ⟨e', he', Fin.ext (by simp [h])⟩
    -- extend by `a ↦ last`
    let f : ι → Fin (r + 2) := fun x =>
      if h : x = a then Fin.last (r + 1) else (e'' ⟨x, h⟩).castSucc
    have hf_a : f a = Fin.last (r + 1) := by simp [f]
    have hf_ne : ∀ x (h : x ≠ a), f x = (e'' ⟨x, h⟩).castSucc := fun x h => by simp [f, h]
    have hinj : Function.Injective f := by
      intro x y hxy
      by_cases hx : x = a <;> by_cases hy : y = a
      · rw [hx, hy]
      · rw [hx, hf_a, hf_ne y hy] at hxy
        exact absurd hxy.symm (Fin.castSucc_ne_last _)
      · rw [hy, hf_a, hf_ne x hx] at hxy
        exact absurd hxy (Fin.castSucc_ne_last _)
      · rw [hf_ne x hx, hf_ne y hy] at hxy
        have := e''.injective (Fin.castSucc_injective _ hxy)
        exact congrArg Subtype.val this
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp [hcard]⟩
    refine ⟨Equiv.ofBijective f hbij, fun x y => ?_⟩
    simp only [Equiv.ofBijective_apply]
    have hlast : ∀ y (hy : y ≠ a), (e'' ⟨y, hy⟩ = Fin.last r ↔ y = b) := by
      intro y hy
      rw [← he''b, e''.apply_eq_iff_eq]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    by_cases hx : x = a <;> by_cases hy : y = a
    · subst hx; subst hy
      rw [hf_a, hdiag, cartanA_last_last]
    · subst hx
      rw [hf_a, hf_ne y hy, cartanA_last_castSucc, hrowa]
      by_cases hyb : y = b
      · have h1 := (hlast y hy).mpr hyb
        simp only [eq_false hy, eq_true hyb, eq_true h1, ↓reduceIte, zero_add]
      · have h1 : ¬ e'' ⟨y, hy⟩ = Fin.last r := fun h => hyb ((hlast y hy).mp h)
        simp only [eq_false hy, eq_false hyb, eq_false h1, ↓reduceIte, add_zero]
    · subst hy
      rw [hf_a, hf_ne x hx, cartanA_symm, cartanA_last_castSucc, hsymm, hrowa]
      by_cases hxb : x = b
      · have h1 := (hlast x hx).mpr hxb
        simp only [eq_false hx, eq_true hxb, eq_true h1, ↓reduceIte, zero_add]
      · have h1 : ¬ e'' ⟨x, hx⟩ = Fin.last r := fun h => hxb ((hlast x hx).mp h)
        simp only [eq_false hx, eq_false hxb, eq_false h1, ↓reduceIte, add_zero]
    · rw [hf_ne x hx, hf_ne y hy, cartanA_castSucc]
      exact he''A ⟨x, hx⟩ ⟨y, hy⟩

/-! ## Vertex-transitive affine extensions -/

/-- **Vertex-transitive affine extensions are of type `A`.** Let `B` be a generalized Cartan
matrix on `Option ι` (diagonal `2`, nonpositive off-diagonal entries, symmetric support) with
a positive integral left kernel vector `m` (`m ᵥ* B = 0`), whose automorphism group acts
transitively on `Option ι`. If the principal submatrix `A = B.submatrix some some` kills no nonzero integral
vector, then `A` is the type-`A` Cartan matrix of rank `card ι > 0` after renumbering. -/
theorem exists_equiv_cartanA_of_transitive {ι : Type u} [Fintype ι] [DecidableEq ι]
    (B : Matrix (Option ι) (Option ι) ℤ)
    (hdiag : ∀ i, B i i = 2) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    (hsupp : ∀ i j, B i j = 0 → B j i = 0)
    (m : Option ι → ℤ) (hm : ∀ i, 0 < m i) (hker : Matrix.vecMul m B = 0)
    (htrans : ∀ i j, ∃ σ : Equiv.Perm (Option ι), (∀ k l, B (σ k) (σ l) = B k l) ∧ σ i = j)
    (hnd : ∀ v : ι → ℤ, (B.submatrix some some).mulVec v = 0 → v = 0) :
    ∃ n, 0 < n ∧ ∃ e : ι ≃ Fin n, ∀ a b, B (some a) (some b) = CartanMatrix.A n (e a) (e b) := by
  -- row and column sums are constant
  have hrowc : ∀ i, ∑ j, B i j = ∑ j, B none j := by
    intro i
    obtain ⟨σ, hσB, hσ⟩ := htrans none i
    rw [← hσ, ← Equiv.sum_comp σ (B (σ none))]
    exact Finset.sum_congr rfl fun j _ => hσB none j
  have hcolc : ∀ j, ∑ i, B i j = ∑ i, B i none := by
    intro j
    obtain ⟨σ, hσB, hσ⟩ := htrans none j
    rw [← hσ, ← Equiv.sum_comp σ (fun i => B i (σ none))]
    exact Finset.sum_congr rfl fun i _ => hσB i none
  have hmpos : 0 < ∑ i, m i := Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  -- row sums vanish, by pairing with the left kernel vector
  have hrow : ∀ i, ∑ j, B i j = 0 := by
    have h1 : ∑ j, ∑ i, m i * B i j = 0 :=
      Finset.sum_eq_zero fun j _ => by simpa [Matrix.vecMul, dotProduct] using congrFun hker j
    have h2 : ∑ j, ∑ i, m i * B i j = (∑ i, m i) * ∑ j, B none j :=
      calc ∑ j, ∑ i, m i * B i j = ∑ i, ∑ j, m i * B i j := Finset.sum_comm
        _ = ∑ i, m i * ∑ j, B none j :=
          Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, hrowc i]
        _ = (∑ i, m i) * ∑ j, B none j := by rw [Finset.sum_mul]
    rw [h2] at h1
    intro i
    rw [hrowc i]
    exact (mul_eq_zero.mp h1).resolve_left hmpos.ne'
  -- column sums vanish, by the total sum
  have hcol : ∀ j, ∑ i, B i j = 0 := by
    have htot : ∑ j, ∑ i, B i j = 0 :=
      calc ∑ j, ∑ i, B i j = ∑ i, ∑ j, B i j := Finset.sum_comm
        _ = 0 := Finset.sum_eq_zero fun i _ => hrow i
    have h3 : ∑ j, ∑ i, B i j = (Fintype.card (Option ι) : ℤ) * ∑ i, B i none := by
      rw [Finset.sum_congr rfl fun j _ => hcolc j]
      simp [Finset.sum_const]
    intro j
    rw [hcolc j]
    rw [h3] at htot
    exact (mul_eq_zero.mp htot).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- the principal submatrix
  set A : Matrix ι ι ℤ := B.submatrix some some with hA
  have hAapp : ∀ a b, A a b = B (some a) (some b) := fun a b => rfl
  have hsA : ∀ a, ∑ b, A a b = - B (some a) none := by
    intro a
    have := hrow (some a)
    rw [Fintype.sum_option] at this
    simp only [hAapp]
    linarith
  have hsumA : ∑ a, ∑ b, A a b = 2 := by
    have := hcol none
    rw [Fintype.sum_option, hdiag] at this
    simp only [hsA, Finset.sum_neg_distrib]
    linarith
  -- closed sets of vertices with zero row sums are empty
  have hclosed : ∀ T : Finset ι, (∀ a ∈ T, ∀ b, A a b ≠ 0 → b ∈ T) →
      (∀ a ∈ T, ∑ b, A a b = 0) → T = ∅ := by
    intro T hT hz
    have hv := hnd (fun b => if b ∈ T then 1 else 0) (by
      funext a
      simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero, Pi.zero_apply]
      by_cases ha : a ∈ T
      · refine (Finset.sum_congr rfl fun b _ => ?_).trans (hz a ha)
        split_ifs with hb
        · rfl
        · by_contra h
          exact hb (hT a ha b (Ne.symm h))
      · refine Finset.sum_eq_zero fun b _ => ?_
        split_ifs with hb
        · by_contra h
          exact ha (hT b hb a (fun h' => h (hsupp _ _ h')))
        · rfl)
    refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
    have := congrFun hv a
    simp [ha] at this
  -- off-diagonal entries are at least `-2`, and an entry `-2` is alone in its row
  have hrow2 : ∀ i j, i ≠ j →
      -2 ≤ B i j ∧ (B i j = -2 → ∀ k, k ≠ i → k ≠ j → B i k = 0) := by
    intro i j hij
    have hsplit : ∑ k, B i k = B i i + B i j + ∑ k ∈ (univ.erase i).erase j, B i k := by
      rw [add_assoc, Finset.add_sum_erase _ _ (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩),
        Finset.add_sum_erase _ _ (mem_univ i)]
    have hnp : ∀ k ∈ (univ.erase i).erase j, B i k ≤ 0 := fun k hk =>
      hoff i k (Ne.symm (ne_of_mem_erase (mem_of_mem_erase hk)))
    have hrest := Finset.sum_nonpos hnp
    rw [hrow i, hdiag] at hsplit
    refine ⟨by linarith, fun h k hki hkj => ?_⟩
    have h0 : ∑ k ∈ (univ.erase i).erase j, B i k = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonpos hnp).mp h0 k
      (mem_erase.mpr ⟨hkj, mem_erase.mpr ⟨hki, mem_univ k⟩⟩)
  have hcol2 : ∀ i j, i ≠ j → B i j = -2 → B j i = -2 := by
    intro i j hij h
    have hz := (hrow2 i j hij).2 h
    have hsplit : ∑ k, B k i = B i i + B j i + ∑ k ∈ (univ.erase i).erase j, B k i := by
      have e1 := Finset.add_sum_erase (univ.erase i) (fun k => B k i)
        (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩)
      have e2 := Finset.add_sum_erase univ (fun k => B k i) (mem_univ i)
      beta_reduce at e1 e2
      linarith
    have h0 : ∑ k ∈ (univ.erase i).erase j, B k i = 0 := Finset.sum_eq_zero fun k hk =>
      hsupp _ _ (hz k (ne_of_mem_erase (mem_of_mem_erase hk)) (ne_of_mem_erase hk))
    rw [hcol i, hdiag, h0] at hsplit
    linarith
  -- hence off-diagonal entries of `A` are `0` or `-1`
  have hoffA : ∀ a b, a ≠ b → A a b = 0 ∨ A a b = -1 := by
    intro a b hab
    have hab' : (some a : Option ι) ≠ some b := fun h => hab (Option.some_injective _ h)
    obtain ⟨hge, hm2⟩ := hrow2 _ _ hab'
    have hle := hoff _ _ hab'
    have hne : B (some a) (some b) ≠ -2 := by
      intro h2
      have h2' := hcol2 _ _ hab' h2
      have hza := hm2 h2
      have hzb := (hrow2 _ _ (Ne.symm hab')).2 h2'
      have hT := hclosed {a, b}
        (by
          intro x hx c hc
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          by_contra hcne
          simp only [not_or] at hcne
          rcases hx with hx | hx
          · rw [hx] at hc
            exact hc (hza (some c) (fun h => hcne.1 (Option.some_injective _ h))
              (fun h => hcne.2 (Option.some_injective _ h)))
          · rw [hx] at hc
            exact hc (hzb (some c) (fun h => hcne.2 (Option.some_injective _ h))
              (fun h => hcne.1 (Option.some_injective _ h))))
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [hsA]
          rcases hx with hx | hx
          · rw [hx, hza none (Option.some_ne_none _).symm (Option.some_ne_none _).symm, neg_zero]
          · rw [hx, hzb none (Option.some_ne_none _).symm (Option.some_ne_none _).symm, neg_zero])
      simp at hT
    simp only [hAapp]
    omega
  have hsymmA : ∀ a b, A a b = A b a := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    have h1 := hoffA a b hab
    have h2 := hoffA b a (Ne.symm hab)
    have h3 : A a b = 0 → A b a = 0 := hsupp _ _
    have h4 : A b a = 0 → A a b = 0 := hsupp _ _
    omega
  have hnonneg : ∀ a, 0 ≤ ∑ b, A a b := fun a => by
    rw [hsA]
    linarith [hoff (some a) none (Option.some_ne_none a)]
  have hcardpos : 0 < Fintype.card ι := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · exfalso
      have := Fintype.card_eq_zero_iff.mp h
      simp at hsumA
    · exact h
  obtain ⟨e, he⟩ := exists_equiv_cartanA_of_path (Fintype.card ι - 1) (by omega) A
    (fun a => hdiag (some a)) hoffA hsymmA hnonneg hsumA hclosed
  exact ⟨_, Nat.succ_pos _, e, he⟩

end AffineCartan

/-! ## The actual Cartan pairings -/

namespace TitsIndexData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The actual Cartan pairings kill no nonzero integral vector: if
`∑ b, ⟨α_a, α_b^∨⟩ v_b = 0` for every simple root `α_a`, then `v = 0`. -/
theorem cartan_mulVec_eq_zero (d : TitsIndexData G) (v : d.Vertex → ℤ)
    (hv : (Matrix.of d.cartan).mulVec v = 0) : v = 0 := by
  classical
  refine Matrix.eq_zero_of_mulVec_eq_zero ?_ hv
  convert Langlands.RootDatum.DominantMultiple.cartan_det_ne_zero d.pinning.rootDatum
    d.pinning.base
  ext a b
  rfl

/-- **Type `A` from a vertex-transitive affine extension of the actual Cartan pairings.**
If the actual Cartan pairings `d.cartan` extend to a generalized Cartan matrix `B` on
`Option d.Vertex` with a positive integral left kernel vector and a vertex-transitive automorphism
group, then the actual index has type `A_n` for some positive `n`. -/
theorem exists_equiv_cartanA_of_transitive_extension (d : TitsIndexData G)
    (B : Matrix (Option d.Vertex) (Option d.Vertex) ℤ)
    (hB : ∀ a b, B (some a) (some b) = d.cartan a b) (h00 : B none none = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hsupp : ∀ i j, B i j = 0 → B j i = 0)
    (m : Option d.Vertex → ℤ) (hm : ∀ i, 0 < m i) (hker : Matrix.vecMul m B = 0)
    (htrans : ∀ i j, ∃ σ : Equiv.Perm (Option d.Vertex),
      (∀ k l, B (σ k) (σ l) = B k l) ∧ σ i = j) :
    ∃ n, 0 < n ∧ ∃ e : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b) := by
  classical
  obtain ⟨n, hn, e, he⟩ := AffineCartan.exists_equiv_cartanA_of_transitive B
    (fun i => by
      cases i with
      | none => exact h00
      | some a => rw [hB]; exact d.pinning.rootDatum.pairing_same a.val)
    hoff hsupp m hm hker htrans
    (fun v hv => d.cartan_mulVec_eq_zero v (by
      rw [← hv]
      funext a
      simp [Matrix.mulVec, dotProduct, hB]))
  exact ⟨n, hn, e, fun a b => (hB a b).symm.trans (he a b)⟩

end TitsIndexData

end Langlands.GroupScheme
