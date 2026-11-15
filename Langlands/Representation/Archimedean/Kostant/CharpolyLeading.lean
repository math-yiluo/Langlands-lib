import Langlands.Representation.Archimedean.Kostant.CharpolyOrder

/-!
# Leading terms of the characteristic polynomial coefficients of a generic block

We prove `CharpolyLeadingStatement n`: for `k < n b`, the leading monomial for `ord n` of the
coefficient of `t^k` of the characteristic polynomial of `genericBlock n b` is
`antidiag n b k`, with leading coefficient `(-1)^(n b - k) * sign (Fin.revPerm) = ±1`.

The coefficient is `(-1)^(n b - k)` times the sum of the principal `(n b - k)`-minors
(`Matrix.charpoly_coeff_eq_sum_minors`). Every term of the minor on the rows and columns `s`
has column weight `∑_{i ∈ s} i`, which is largest exactly for the final segment
`seg n b k = {k, …, n b - 1}`. In that minor the term of the reversal permutation, whose
exponent is `antidiag n b k`, is lexicographically largest.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

open MvPolynomial Finset
open scoped MonomialOrder

namespace CharpolyLeading

section Degree

variable {σ R α : Type*} [CommRing R] (m : MonomialOrder σ)

/-- A nonempty sum of polynomials whose degrees are all below `D` has degree below `D`. -/
theorem degree_sum_lt {s : Finset α} {f : α → MvPolynomial σ R} {D : σ →₀ ℕ}
    (hs : s.Nonempty) (h : ∀ x ∈ s, m.degree (f x) ≺[m] D) :
    m.degree (∑ x ∈ s, f x) ≺[m] D := by
  obtain ⟨x, hx⟩ := hs
  have hbot : (⊥ : m.syn) < m.toSyn D := lt_of_le_of_lt bot_le (h x hx)
  exact lt_of_le_of_lt m.degree_sum_le ((Finset.sup_lt_iff hbot).2 h)

/-- If one summand has strictly larger degree than all the others, it determines the degree
and the leading coefficient of the sum. -/
theorem degree_sum_eq_of_unique {T : Finset α} {f : α → MvPolynomial σ R} {x₀ : α}
    (hx₀ : x₀ ∈ T) (hlt : ∀ x ∈ T, x ≠ x₀ → m.degree (f x) ≺[m] m.degree (f x₀)) :
    m.degree (∑ x ∈ T, f x) = m.degree (f x₀) ∧
      m.leadingCoeff (∑ x ∈ T, f x) = m.leadingCoeff (f x₀) := by
  classical
  rw [← Finset.add_sum_erase T f hx₀]
  rcases (T.erase x₀).eq_empty_or_nonempty with he | hne
  · simp [he]
  · have h := degree_sum_lt m hne fun x hx =>
      hlt x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
    exact ⟨m.degree_add_of_lt h, m.leadingCoeff_add_of_lt h⟩

theorem degree_monomial_of_ne {d : σ →₀ ℕ} {c : R} (hc : c ≠ 0) :
    m.degree (monomial d c) = d := by
  classical
  rw [MonomialOrder.degree_monomial]
  exact ite_eq_right_iff.2 fun h => absurd h hc

theorem weight_sum_single [Fintype α] (w : σ → ℕ) (h : α → σ) :
    Finsupp.weight w (∑ j, Finsupp.single (h j) 1) = ∑ j, w (h j) := by
  rw [map_sum]
  simp only [Finsupp.weight_single, one_smul]

end Degree

/-- Among the subsets of `Fin N` with as many elements as the final segment `s₀ = {i | k ≤ i}`,
the sum of the elements is largest exactly for `s₀`. -/
theorem sum_lt_sum_of_mem_iff {N k : ℕ} {s s₀ : Finset (Fin N)}
    (hmem : ∀ i, i ∈ s₀ ↔ k ≤ (i : ℕ)) (hcard : s.card = s₀.card) (hs : s ≠ s₀) :
    ∑ i ∈ s, (i : ℕ) < ∑ i ∈ s₀, (i : ℕ) := by
  have hne : (s \ s₀).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hs (Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.1 h) hcard.ge)
  have hc : (s \ s₀).card = (s₀ \ s).card := Finset.card_sdiff_comm hcard
  have h1 : ∑ i ∈ s \ s₀, (i : ℕ) < (s \ s₀).card * k := by
    have := Finset.sum_lt_sum_of_nonempty hne (f := fun i : Fin N => (i : ℕ)) (g := fun _ => k)
      (fun i hi => by
        have h := (Finset.mem_sdiff.1 hi).2
        rw [hmem] at h
        exact not_le.1 h)
    simpa [mul_comm] using this
  have h2 : (s₀ \ s).card * k ≤ ∑ i ∈ s₀ \ s, (i : ℕ) := by
    have := Finset.card_nsmul_le_sum (s₀ \ s) (fun i : Fin N => (i : ℕ)) k (fun i hi =>
      (hmem i).1 (Finset.mem_sdiff.1 hi).1)
    simpa using this
  rw [hc] at h1
  rw [← Finset.sum_inter_add_sum_sdiff s s₀, ← Finset.sum_inter_add_sum_sdiff s₀ s,
    Finset.inter_comm]
  omega

/-- A permutation of `Fin M` other than the reversal differs from it at a largest column `c`,
and there it takes a larger value. -/
theorem exists_lt_rev {M : ℕ} {τ : Equiv.Perm (Fin M)} (hτ : τ ≠ Fin.revPerm) :
    ∃ c : Fin M, Fin.rev c < τ c ∧ ∀ j, c < j → τ j = Fin.rev j := by
  classical
  have hex : (univ.filter fun j : Fin M => τ j ≠ Fin.rev j).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hτ (Equiv.ext fun j => by simpa using h (Finset.mem_univ j))
  set c := (univ.filter fun j : Fin M => τ j ≠ Fin.rev j).max' hex
  have hc : τ c ≠ Fin.rev c := (Finset.mem_filter.1 (Finset.max'_mem _ hex)).2
  have hgt : ∀ j, c < j → τ j = Fin.rev j := by
    intro j hj
    by_contra h
    exact absurd (Finset.le_max' _ j (by simp [h])) (not_le.2 hj)
  refine ⟨c, lt_of_le_of_ne ?_ (Ne.symm hc), hgt⟩
  by_contra hlt
  rw [not_le] at hlt
  -- `τ c = rev j` for `j = rev (τ c) > c`, and `τ j = rev j`, so `τ c = τ j` and `c = j`.
  have hj : c < Fin.rev (τ c) := Fin.lt_rev_iff.2 hlt
  have := hgt _ hj
  rw [Fin.rev_rev] at this
  exact absurd (τ.injective this).symm (ne_of_lt hj)

theorem sign_cast_ne_zero {α : Type*} [Fintype α] [DecidableEq α] (τ : Equiv.Perm α) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) ≠ 0 :=
  Int.cast_ne_zero.2 (Units.ne_zero _)

variable {ι : Type} (n : ι → ℕ)

section Monomials

variable {α : Type*} [Fintype α]

/-- The exponent `∑ⱼ e_{h j}` of the monomial `∏ⱼ X (h j)`. -/
def expo (h : α → Coord n) : Coord n →₀ ℕ :=
  ∑ j, Finsupp.single (h j) 1

theorem C_mul_prod_X (h : α → Coord n) (c : ℂ) :
    C c * ∏ j, (X (h j) : MvPolynomial (Coord n) ℂ) = monomial (expo n h) c := by
  rw [expo, monomial_sum_index]
  rfl

theorem expo_apply_self {h : α → Coord n} (hh : Function.Injective h) (j : α) :
    expo n h (h j) = 1 := by
  classical
  rw [expo, Finsupp.finsetSum_apply, Finset.sum_eq_single j
    (fun i _ hi => Finsupp.single_eq_of_ne' (hh.ne hi))
    (fun hj => absurd (Finset.mem_univ j) hj), Finsupp.single_eq_same]

theorem expo_apply_eq_zero {h : α → Coord n} {c : Coord n} (hc : ∀ j, h j ≠ c) :
    expo n h c = 0 := by
  classical
  rw [expo, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne' (hc j)

/-- Expansion of a determinant of variables into signed monomials. -/
theorem det_eq_sum_monomial [DecidableEq α] (M : Matrix α α (MvPolynomial (Coord n) ℂ))
    (g : α → α → Coord n) (hM : ∀ p q, M p q = X (g p q)) :
    M.det = ∑ τ : Equiv.Perm α,
      monomial (expo n fun j => g (τ j) j) ((Equiv.Perm.sign τ : ℤ) : ℂ) := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← C_mul_prod_X, map_intCast]
  simp only [hM]

end Monomials

section Block

/-- The shift `j ↦ k + j` from `Fin (n b - k)` onto the final segment of `Fin (n b)`. -/
def sh (b : ι) (k : ℕ) (j : Fin (n b - k)) : Fin (n b) :=
  ⟨k + j, by have := j.2; omega⟩

theorem sh_val (b : ι) (k : ℕ) (j : Fin (n b - k)) : (sh n b k j : ℕ) = k + j := rfl

theorem sh_injective (b : ι) (k : ℕ) : Function.Injective (sh n b k) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [sh_val] at this
  exact Fin.ext (by omega)

/-- The final segment `{k, …, n b - 1}` of `Fin (n b)`, as the image of `sh`. -/
def seg (b : ι) (k : ℕ) : Finset (Fin (n b)) :=
  Finset.univ.image (sh n b k)

theorem mem_seg (b : ι) (k : ℕ) (i : Fin (n b)) : i ∈ seg n b k ↔ k ≤ (i : ℕ) := by
  constructor
  · intro hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
    rw [sh_val]
    omega
  · intro hi
    have := i.2
    refine Finset.mem_image.2 ⟨⟨i - k, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
    show k + ((i : ℕ) - k) = i
    omega

theorem card_seg (b : ι) (k : ℕ) : (seg n b k).card = n b - k := by
  rw [seg, Finset.card_image_of_injective _ (sh_injective n b k), Finset.card_univ,
    Fintype.card_fin]

theorem sum_seg (b : ι) (k : ℕ) :
    ∑ i ∈ seg n b k, (i : ℕ) = ∑ j, (sh n b k j : ℕ) :=
  Finset.sum_image fun _ _ _ _ h => sh_injective n b k h

/-- `Fin (n b - k)` enumerates the final segment. -/
def segEquiv (b : ι) (k : ℕ) : Fin (n b - k) ≃ seg n b k :=
  Equiv.ofBijective (fun j => ⟨sh n b k j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
    ⟨fun _ _ h => sh_injective n b k (congrArg Subtype.val h), fun ⟨_, hi⟩ => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
      exact ⟨j, rfl⟩⟩

/-- The coordinate in row `k + p` and column `k + q` of block `b`. -/
def ent (b : ι) (k : ℕ) (p q : Fin (n b - k)) : Coord n :=
  ⟨b, sh n b k p, sh n b k q⟩

theorem ent_eq_ent_iff {b : ι} {k : ℕ} {p q p' q' : Fin (n b - k)} :
    ent n b k p q = ent n b k p' q' ↔ p = p' ∧ q = q' := by
  simp [ent, (sh_injective n b k).eq_iff]

/-- The exponent of the term of the permutation `τ` in the minor of the final segment. -/
def permExpo (b : ι) (k : ℕ) (τ : Equiv.Perm (Fin (n b - k))) : Coord n →₀ ℕ :=
  expo n fun j => ent n b k (τ j) j

theorem ent_perm_injective (b : ι) (k : ℕ) (τ : Equiv.Perm (Fin (n b - k))) :
    Function.Injective fun j => ent n b k (τ j) j :=
  fun _ _ h => (ent_eq_ent_iff n).1 h |>.2

theorem permExpo_apply_ent (b : ι) (k : ℕ) (τ : Equiv.Perm (Fin (n b - k))) (j : Fin (n b - k)) :
    permExpo n b k τ (ent n b k (τ j) j) = 1 :=
  expo_apply_self n (h := fun j => ent n b k (τ j) j) (ent_perm_injective n b k τ) j

theorem weight_expo {α : Type*} [Fintype α] (h : α → Coord n) :
    Finsupp.weight (colWeight n) (expo n h) = ∑ j, colWeight n (h j) :=
  weight_sum_single (σ := PCoord n) (colWeight n) h

variable [Fintype ι]

/-- A coordinate viewed in the variable order `PCoord n`. -/
def toP (c : Coord n) : PCoord n := c

/-- In the variable order, a larger column comes first, and in the same column a smaller row
comes first. -/
theorem ent_lt_ent_iff {b : ι} {k : ℕ} {p q p' q' : Fin (n b - k)} :
    toP n (ent n b k p q) < toP n (ent n b k p' q') ↔ q' < q ∨ (q = q' ∧ p < p') := by
  rw [PCoord.lt_iff]
  simp only [toP, ent, prio, Prod.Lex.toLex_lt_toLex, lt_irrefl, false_or, true_and,
    OrderDual.toDual_lt_toDual, OrderDual.toDual_inj, sh_val, Fin.lt_def, Fin.ext_iff]
  constructor
  · rintro (h | ⟨h1, h2⟩) <;> omega
  · rintro (h | ⟨h1, h2⟩) <;> omega

/-- The reversal permutation gives the antidiagonal monomial. -/
theorem permExpo_rev {b : ι} {k : ℕ} (hk : k < n b) :
    permExpo n b k Fin.revPerm = antidiag n b k := by
  classical
  ext c
  rw [antidiag_apply]
  obtain ⟨b', p, q⟩ := c
  split_ifs with h
  · obtain ⟨hb, hpq⟩ := h
    dsimp only at hb hpq
    subst b'
    have hp := p.2
    have hq := q.2
    let j : Fin (n b - k) := ⟨q - k, by omega⟩
    have h1 : sh n b k j = q := Fin.ext (by rw [sh_val]; show k + ((q : ℕ) - k) = q; omega)
    have h2 : sh n b k (Fin.rev j) = p := Fin.ext (by
      rw [sh_val, Fin.val_rev]
      show k + (n b - k - ((q : ℕ) - k + 1)) = p
      omega)
    have := permExpo_apply_ent n b k Fin.revPerm j
    rwa [show ent n b k (Fin.revPerm j) j = ⟨b, p, q⟩ by
      rw [ent, Fin.revPerm_apply, h1, h2]] at this
  · refine expo_apply_eq_zero n fun j hj => h ?_
    simp only [ent, Fin.revPerm_apply, Sigma.mk.injEq] at hj
    obtain ⟨hb, hj⟩ := hj
    subst b'
    simp only [heq_eq_eq, Prod.mk.injEq] at hj
    obtain ⟨rfl, rfl⟩ := hj
    refine ⟨rfl, ?_⟩
    dsimp only
    have := j.2
    rw [sh_val, sh_val, Fin.val_rev]
    omega

/-- For a permutation other than the reversal, the exponent is smaller than the antidiagonal
one: both have the same column weight, and at the variable `X (ent (rev c) c)` of the largest
column `c` where they differ, only the reversal has exponent `1`. -/
theorem permExpo_lt_rev {b : ι} {k : ℕ} {τ : Equiv.Perm (Fin (n b - k))}
    (hτ : τ ≠ Fin.revPerm) :
    permExpo n b k τ ≺[ord n] permExpo n b k Fin.revPerm := by
  rw [ord_lt_iff]
  right
  refine ⟨by rw [permExpo, permExpo, weight_expo, weight_expo]; rfl, ?_⟩
  obtain ⟨c, hc, hgt⟩ := exists_lt_rev hτ
  -- below the variable `v = ent (rev c) c`, the two permutations use the same variables
  have key₁ : ∀ j, toP n (ent n b k (τ j) j) < toP n (ent n b k (Fin.rev c) c) →
      τ j = Fin.revPerm j := by
    intro j hj
    rcases (ent_lt_ent_iff n).1 hj with h | ⟨rfl, h⟩
    · exact hgt j h
    · exact absurd hc (not_lt.2 h.le)
  have key₂ : ∀ j, toP n (ent n b k (Fin.revPerm j) j) < toP n (ent n b k (Fin.rev c) c) →
      τ j = Fin.revPerm j := by
    intro j hj
    rcases (ent_lt_ent_iff n).1 hj with h | ⟨rfl, h⟩
    · exact hgt j h
    · exact absurd h (lt_irrefl _)
  refine Finsupp.Lex.lt_iff.2 ⟨toP n (ent n b k (Fin.rev c) c), fun d hd => ?_, ?_⟩
  · show permExpo n b k τ d = permExpo n b k Fin.revPerm d
    by_cases hex : ∃ j, ent n b k (τ j) j = d
    · obtain ⟨j, rfl⟩ := hex
      have e := key₁ j hd
      rw [permExpo_apply_ent, e, permExpo_apply_ent]
    · have hex' : ∀ j, ent n b k (Fin.revPerm j) j ≠ d := by
        rintro j rfl
        exact hex ⟨j, by rw [key₂ j hd]⟩
      rw [permExpo, permExpo, expo_apply_eq_zero n fun j hj => hex ⟨j, hj⟩,
        expo_apply_eq_zero n hex']
  · show permExpo n b k τ (ent n b k (Fin.rev c) c) <
      permExpo n b k Fin.revPerm (ent n b k (Fin.rev c) c)
    have h1 := permExpo_apply_ent n b k Fin.revPerm c
    rw [Fin.revPerm_apply] at h1
    have h0 : permExpo n b k τ (ent n b k (Fin.rev c) c) = 0 :=
      expo_apply_eq_zero n fun j hj => by
        obtain ⟨h₁, rfl⟩ := (ent_eq_ent_iff n).1 hj
        exact hc.ne' h₁
    rw [h1, h0]
    exact zero_lt_one

/-- Every principal minor other than the one of the final segment has degree below the
antidiagonal monomial, since its column weight is smaller. -/
theorem minor_degree_lt {b : ι} {k : ℕ} (hk : k < n b) {s : Finset (Fin (n b))}
    (hs : s.card = n b - k) (hne : s ≠ seg n b k) :
    (ord n).degree ((genericBlock n b).submatrix (Subtype.val : s → Fin (n b)) Subtype.val).det
      ≺[ord n] antidiag n b k := by
  classical
  rw [det_eq_sum_monomial n ((genericBlock n b).submatrix (Subtype.val : s → Fin (n b))
    Subtype.val) (fun p q => (⟨b, p.1, q.1⟩ : Coord n)) (fun p q => rfl)]
  refine degree_sum_lt _ Finset.univ_nonempty fun τ _ => ?_
  rw [degree_monomial_of_ne _ (sign_cast_ne_zero τ), ← permExpo_rev n hk, ord_lt_iff]
  left
  rw [weight_expo, permExpo, weight_expo]
  show ∑ i : s, ((i : Fin (n b)) : ℕ) < ∑ j, (sh n b k j : ℕ)
  rw [Finset.sum_coe_sort s Fin.val, ← sum_seg]
  exact sum_lt_sum_of_mem_iff (mem_seg n b k) (by rw [hs, card_seg]) hne

/-- The minor of the final segment has leading monomial `antidiag n b k` and leading
coefficient `sign (Fin.revPerm)`. -/
theorem seg_minor_leading {b : ι} {k : ℕ} (hk : k < n b) :
    (ord n).degree
        ((genericBlock n b).submatrix (Subtype.val : seg n b k → Fin (n b)) Subtype.val).det =
      antidiag n b k ∧
    (ord n).leadingCoeff
        ((genericBlock n b).submatrix (Subtype.val : seg n b k → Fin (n b)) Subtype.val).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n b - k))) : ℤ) : ℂ) := by
  classical
  rw [← Matrix.det_submatrix_equiv_self (segEquiv n b k),
    det_eq_sum_monomial n (((genericBlock n b).submatrix (Subtype.val : seg n b k → Fin (n b))
      Subtype.val).submatrix (segEquiv n b k) (segEquiv n b k)) (ent n b k) (fun p q => rfl)]
  have h := degree_sum_eq_of_unique (ord n) (T := Finset.univ)
    (f := fun τ : Equiv.Perm (Fin (n b - k)) =>
      monomial (permExpo n b k τ) ((Equiv.Perm.sign τ : ℤ) : ℂ))
    (Finset.mem_univ Fin.revPerm) (fun τ _ hτ => by
      rw [degree_monomial_of_ne _ (sign_cast_ne_zero _),
        degree_monomial_of_ne _ (sign_cast_ne_zero _)]
      exact permExpo_lt_rev n hτ)
  rw [degree_monomial_of_ne _ (sign_cast_ne_zero _), MonomialOrder.leadingCoeff_monomial] at h
  rw [← permExpo_rev n hk]
  exact h

end Block

end CharpolyLeading

variable {ι : Type} [Fintype ι] (n : ι → ℕ)

open CharpolyLeading in
/-- **Leading terms of the characteristic polynomial coefficients** of the generic blocks. -/
theorem charpolyLeading : CharpolyLeadingStatement n := by
  intro b k hk
  classical
  have hcoeff := Matrix.charpoly_coeff_eq_sum_minors (genericBlock n b) (n b - k)
    (by rw [Fintype.card_fin]; omega)
  rw [Fintype.card_fin, Nat.sub_sub_self hk.le] at hcoeff
  rw [hcoeff]
  have hseg : seg n b k ∈ Finset.univ.powersetCard (n b - k) :=
    Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, card_seg n b k⟩
  obtain ⟨h₀, l₀⟩ := seg_minor_leading n hk
  obtain ⟨hdeg, hlc⟩ := degree_sum_eq_of_unique (ord n)
    (f := fun s : Finset (Fin (n b)) =>
      ((genericBlock n b).submatrix (Subtype.val : s → Fin (n b)) Subtype.val).det)
    hseg (fun s hs hne => by
      rw [h₀]
      exact minor_degree_lt n hk (Finset.mem_powersetCard.1 hs).2 hne)
  have hC : ((-1 : MvPolynomial (Coord n) ℂ)) ^ (n b - k) = C ((-1) ^ (n b - k)) := by
    simp
  have hne : (ord n).leadingCoeff (C ((-1 : ℂ) ^ (n b - k))) *
      (ord n).leadingCoeff (∑ s ∈ Finset.univ.powersetCard (n b - k),
        ((genericBlock n b).submatrix (Subtype.val : s → Fin (n b)) Subtype.val).det) ≠ 0 := by
    rw [hlc, l₀, MonomialOrder.leadingCoeff_C]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (sign_cast_ne_zero _)
  rw [hC, MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero hne,
    MonomialOrder.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero hne, MonomialOrder.degree_C,
    zero_add, hdeg, h₀]
  exact ⟨rfl, isUnit_iff_ne_zero.2 hne⟩

end Langlands.Archimedean.Kostant
