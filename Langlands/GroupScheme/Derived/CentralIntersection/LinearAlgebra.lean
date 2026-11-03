import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.GroupWithZero.Idempotent

/-! # Linear algebra for the central intersection finiteness proof

Elementary facts used by the scheme-theoretic argument: locally unipotent elements for a
ring endomorphism, common kernel vectors of commuting nilpotent families, block projectors
and their determinants, and an idempotent splitting of an annihilating polynomial. -/

noncomputable section

open Polynomial

namespace Langlands.GroupScheme.CentralIntersection

/-! ### Locally unipotent elements of a ring endomorphism -/

section Translation

variable {A : Type*} [CommRing A] (φ : A →+* A)

/-- The difference operator `f ↦ φ f - f` of a ring endomorphism. -/
def diff : A →+ A := φ.toAddMonoidHom - AddMonoidHom.id A

theorem diff_apply (f : A) : diff φ f = φ f - f := rfl

theorem diff_mul (f g : A) : diff φ (f * g) = diff φ f * φ g + f * diff φ g := by
  simp only [diff_apply, map_mul]
  ring

theorem diff_comp (f : A) : diff φ (φ f) = φ (diff φ f) := by
  simp only [diff_apply, map_sub]

theorem iterate_diff_comp (k : ℕ) (f : A) : (diff φ)^[k] (φ f) = φ ((diff φ)^[k] f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, diff_comp, ih]

theorem iterate_diff_zero (k : ℕ) : (diff φ)^[k] (0 : A) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_zero, ih]

theorem iterate_diff_add (k : ℕ) (f g : A) :
    (diff φ)^[k] (f + g) = (diff φ)^[k] f + (diff φ)^[k] g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_add, ih]; rfl

theorem iterate_diff_neg (k : ℕ) (f : A) : (diff φ)^[k] (-f) = -(diff φ)^[k] f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_neg, ih]; rfl

theorem iterate_diff_eq_zero_of_le {k l : ℕ} (hkl : k ≤ l) {f : A}
    (hf : (diff φ)^[k] f = 0) : (diff φ)^[l] f = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [add_comm, Function.iterate_add_apply, hf, iterate_diff_zero]

/-- Twisted Leibniz bound: the product of elements killed by `(φ - 1)^a` and `(φ - 1)^b` is
killed by `(φ - 1)^(a + b)`. -/
theorem iterate_diff_mul_eq_zero (n : ℕ) :
    ∀ (a b : ℕ) (f g : A), a + b = n → (diff φ)^[a] f = 0 → (diff φ)^[b] g = 0 →
      (diff φ)^[n] (f * g) = 0 := by
  induction n with
  | zero =>
    intro a b f g hab hf _
    have ha : a = 0 := by omega
    subst ha
    simp only [Function.iterate_zero, id_eq] at hf ⊢
    rw [hf, zero_mul]
  | succ n ih =>
    intro a b f g hab hf hg
    rcases a with _ | a
    · simp only [Function.iterate_zero, id_eq] at hf
      rw [hf, zero_mul, iterate_diff_zero]
    rcases b with _ | b
    · simp only [Function.iterate_zero, id_eq] at hg
      rw [hg, mul_zero, iterate_diff_zero]
    rw [Function.iterate_succ_apply, diff_mul, iterate_diff_add]
    have h1 : (diff φ)^[n] (diff φ f * φ g) = 0 := by
      refine ih a (b + 1) _ _ (by omega) ?_ ?_
      · rwa [← Function.iterate_succ_apply]
      · rw [iterate_diff_comp, hg, map_zero]
    have h2 : (diff φ)^[n] (f * diff φ g) = 0 := by
      refine ih (a + 1) b _ _ (by omega) hf ?_
      rwa [← Function.iterate_succ_apply]
    rw [h1, h2, add_zero]

/-- The subring of elements on which `φ - 1` is nilpotent. -/
def locallyUnipotent : Subring A where
  carrier := {f | ∃ k : ℕ, (diff φ)^[k] f = 0}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, iterate_diff_mul_eq_zero φ (a + b) a b f g rfl ha hb⟩
  one_mem' := ⟨1, by simp [diff_apply]⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨max a b, ?_⟩
    rw [iterate_diff_add, iterate_diff_eq_zero_of_le φ (le_max_left a b) ha,
      iterate_diff_eq_zero_of_le φ (le_max_right a b) hb, add_zero]
  zero_mem' := ⟨0, rfl⟩
  neg_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨a, by rw [iterate_diff_neg, ha, neg_zero]⟩

theorem mem_locallyUnipotent {f : A} :
    f ∈ locallyUnipotent φ ↔ ∃ k : ℕ, (diff φ)^[k] f = 0 :=
  Iff.rfl

theorem mem_locallyUnipotent_of_fixed {f : A} (hf : φ f = f) : f ∈ locallyUnipotent φ :=
  ⟨1, by simp [diff_apply, hf]⟩

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise iteration of the difference operator on a matrix. -/
theorem iterate_diff_matrix (k : ℕ) (M : Matrix n n A) (i j : n) :
    ((fun N : Matrix n n A => φ.mapMatrix N - N)^[k] M) i j = (diff φ)^[k] (M i j) := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1

/-- If `φ` acts on `M` by right multiplication by a `φ`-fixed matrix `B`, then the iterated
difference operator acts by right multiplication by `(B - 1)^k`. -/
theorem iterate_diff_matrix_eq_mul (M B : Matrix n n A) (hB : φ.mapMatrix B = B)
    (hM : φ.mapMatrix M = M * B) (k : ℕ) :
    (fun N : Matrix n n A => φ.mapMatrix N - N)^[k] M = M * (B - 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hBk : φ.mapMatrix ((B - 1) ^ k) = (B - 1) ^ k := by
      rw [map_pow, map_sub, map_one, hB]
    rw [map_mul, hBk, hM, pow_succ']
    noncomm_ring

/-- If `φ` acts on `M` by left multiplication by a `φ`-fixed matrix `B`, then the iterated
difference operator acts by left multiplication by `(B - 1)^k`. -/
theorem iterate_diff_matrix_eq_mul_left (M B : Matrix n n A) (hB : φ.mapMatrix B = B)
    (hM : φ.mapMatrix M = B * M) (k : ℕ) :
    (fun N : Matrix n n A => φ.mapMatrix N - N)^[k] M = (B - 1) ^ k * M := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hBk : φ.mapMatrix ((B - 1) ^ k) = (B - 1) ^ k := by
      rw [map_pow, map_sub, map_one, hB]
    rw [map_mul, hBk, hM, pow_succ, mul_assoc, sub_mul, one_mul, mul_sub]

/-- Entries of a matrix moved by a unipotent right multiplication are locally unipotent. -/
theorem mem_locallyUnipotent_of_mapMatrix_eq_mul (M B : Matrix n n A)
    (hB : φ.mapMatrix B = B) (hM : φ.mapMatrix M = M * B) (hnil : IsNilpotent (B - 1))
    (i j : n) : M i j ∈ locallyUnipotent φ := by
  obtain ⟨k, hk⟩ := hnil
  refine ⟨k, ?_⟩
  rw [← iterate_diff_matrix, iterate_diff_matrix_eq_mul φ M B hB hM, hk, mul_zero]
  rfl

/-- Entries of a matrix moved by a unipotent left multiplication are locally unipotent. -/
theorem mem_locallyUnipotent_of_mapMatrix_eq_mul_left (M B : Matrix n n A)
    (hB : φ.mapMatrix B = B) (hM : φ.mapMatrix M = B * M) (hnil : IsNilpotent (B - 1))
    (i j : n) : M i j ∈ locallyUnipotent φ := by
  obtain ⟨k, hk⟩ := hnil
  refine ⟨k, ?_⟩
  rw [← iterate_diff_matrix, iterate_diff_matrix_eq_mul_left φ M B hB hM, hk, zero_mul]
  rfl

/-- If every entry of an invertible matrix `M` is locally unipotent and `φ` acts on `M` by
right multiplication by a `φ`-fixed matrix `B`, then `B - 1` is nilpotent. -/
theorem isNilpotent_sub_one_of_mapMatrix_eq_mul (M B : Matrix n n A) (hMu : IsUnit M)
    (hB : φ.mapMatrix B = B) (hM : φ.mapMatrix M = M * B)
    (hloc : ∀ i j, M i j ∈ locallyUnipotent φ) : IsNilpotent (B - 1) := by
  classical
  choose k hk using hloc
  let K := ∑ i, ∑ j, k i j
  refine ⟨K, ?_⟩
  have hzero : (fun N : Matrix n n A => φ.mapMatrix N - N)^[K] M = 0 := by
    ext i j
    rw [iterate_diff_matrix]
    refine iterate_diff_eq_zero_of_le φ ?_ (hk i j)
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (k i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i _ => Nat.zero_le (∑ j, k i j)) (Finset.mem_univ i))
  rw [iterate_diff_matrix_eq_mul φ M B hB hM] at hzero
  obtain ⟨u, rfl⟩ := hMu
  have := congrArg (fun N => (↑u⁻¹ : Matrix n n A) * N) hzero
  simpa [← mul_assoc] using this

end Translation

/-! ### Common kernel vectors of commuting nilpotent families -/

section CommonKernel

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- A nilpotent endomorphism preserving a nonzero subspace kills a nonzero vector of it. -/
theorem exists_mem_ne_zero_apply_eq_zero {a : Module.End K V} (ha : IsNilpotent a)
    {W : Submodule K V} (hW : ∀ w ∈ W, a w ∈ W) {w : V} (hw : w ∈ W) (hw0 : w ≠ 0) :
    ∃ x ∈ W, x ≠ 0 ∧ a x = 0 := by
  classical
  obtain ⟨k, hk⟩ := ha
  have hex : ∃ j : ℕ, (a ^ (j + 1)) w = 0 := ⟨k, by
    rw [pow_succ, hk, zero_mul]
    rfl⟩
  let j := Nat.find hex
  have hj : (a ^ (j + 1)) w = 0 := Nat.find_spec hex
  have hmem : ∀ i : ℕ, (a ^ i) w ∈ W := by
    intro i
    induction i with
    | zero => simpa using hw
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hW _ ih
  refine ⟨(a ^ j) w, hmem j, ?_, ?_⟩
  · rcases hj0 : j with _ | j'
    · simpa using hw0
    · have hlt : j' < j := by omega
      have := Nat.find_min hex hlt
      exact this
  · rw [← Module.End.mul_apply, ← pow_succ']
    exact hj

/-- A pairwise commuting family of nilpotent endomorphisms of a nonzero finite-dimensional
vector space has a nonzero common kernel vector. -/
theorem exists_ne_zero_forall_eq_zero [Nontrivial V] (s : Set (Module.End K V))
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, Commute a b) (hnil : ∀ a ∈ s, IsNilpotent a) :
    ∃ v : V, v ≠ 0 ∧ ∀ a ∈ s, a v = 0 := by
  classical
  let 𝒮 : Set (Submodule K V) := {W | W ≠ ⊥ ∧ ∀ a ∈ s, ∀ w ∈ W, a w ∈ W}
  have hne : 𝒮.Nonempty := ⟨⊤, top_ne_bot, fun _ _ _ _ => Submodule.mem_top⟩
  obtain ⟨W, ⟨hW0, hWinv⟩, hmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min 𝒮 hne
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  refine ⟨w, hw0, fun a ha => ?_⟩
  let W' : Submodule K V := W ⊓ LinearMap.ker a
  have hW'𝒮 : W' ∈ 𝒮 := by
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hxW, hx0, hax⟩ :=
        exists_mem_ne_zero_apply_eq_zero (hnil a ha) (hWinv a ha) hwW hw0
      intro hbot
      have : x ∈ W' := ⟨hxW, hax⟩
      rw [hbot, Submodule.mem_bot] at this
      exact hx0 this
    · intro b hb x hx
      refine ⟨hWinv b hb x hx.1, ?_⟩
      change a (b x) = 0
      rw [← Module.End.mul_apply, (hcomm a ha b hb).eq, Module.End.mul_apply]
      have hx2 : a x = 0 := hx.2
      rw [hx2, map_zero]
  have hle : W' ≤ W := inf_le_left
  have heq : W' = W := by
    by_contra hne'
    exact hmin W' hW'𝒮 (lt_of_le_of_ne hle hne')
  have : w ∈ W' := heq ▸ hwW
  exact this.2

end CommonKernel

/-! ### Block projectors -/

section Block

variable {K : Type*} [Field K]

/-- A multiset of elements each equal to `c` or `1` has product `c` to the number of
occurrences of `c`. -/
theorem multiset_prod_eq_pow_count [DecidableEq K] (c : K) (s : Multiset K)
    (h : ∀ x ∈ s, x = c ∨ x = 1) : s.prod = c ^ s.count c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hs : ∀ x ∈ s, x = c ∨ x = 1 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.prod_cons, ih hs, Multiset.count_cons]
    rcases h a (Multiset.mem_cons_self a s) with rfl | rfl
    · simp [pow_succ, mul_comm]
    · by_cases h1 : (1 : K) = c
      · subst h1
        simp
      · simp [Ne.symm h1]

variable [IsAlgClosed K] {n : Type*} [Fintype n] [DecidableEq n]

/-- For an eigenvalue `c` of a matrix `A₀`, the idempotent polynomial in `A₀` projecting onto
the generalized `c`-eigenspace along the other generalized eigenspaces, and the determinant
of `A₀` on that block: `det (A₀ π + (1 - π)) = c ^ a` with `1 ≤ a ≤ card n`. -/
theorem exists_blockProjector (A₀ : Matrix n n K) {c : K} (hc : A₀.charpoly.IsRoot c) :
    ∃ P : K[X], IsIdempotentElem (aeval A₀ P) ∧
      ∃ a : ℕ, 1 ≤ a ∧ a ≤ Fintype.card n ∧
        (A₀ * aeval A₀ P + (1 - aeval A₀ P)).det = c ^ a := by
  classical
  set q := A₀.charpoly with hqdef
  have hq0 : q ≠ 0 := A₀.charpoly_monic.ne_zero
  obtain ⟨r, hq, hr⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq0 c
  set m := q.rootMultiplicity c with hmdef
  have hm : 0 < m := (rootMultiplicity_pos hq0).2 hc
  obtain ⟨u, w, huw⟩ :=
    ((irreducible_X_sub_C c).coprime_pow_of_not_dvd m hr).symm
  -- `huw : u * (X - C c) ^ m + w * r = 1`
  set P : K[X] := w * r with hPdef
  refine ⟨P, ?_, ?_⟩
  · have h1 : aeval A₀ (u * (X - C c) ^ m) = 1 - aeval A₀ P := by
      rw [eq_sub_iff_add_eq, ← map_add, huw, map_one]
    have h2 : aeval A₀ P * aeval A₀ (u * (X - C c) ^ m) = 0 := by
      rw [← map_mul]
      have : P * (u * (X - C c) ^ m) = w * u * q := by
        rw [hq, hPdef]
        ring
      rw [this, map_mul, Matrix.aeval_self_charpoly, mul_zero]
    rw [h1, mul_sub, mul_one, sub_eq_zero] at h2
    exact h2.symm
  · set G : K[X] := X * P + (1 - P) with hGdef
    have hY : A₀ * aeval A₀ P + (1 - aeval A₀ P) = aeval A₀ G := by
      simp [hGdef]
    have hPc : P.eval c = 1 := by
      have := congrArg (eval c) huw
      simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
        zero_pow hm.ne', mul_zero, zero_add, eval_one] at this
      simpa [hPdef] using this
    have hσX : c ∈ spectrum K A₀ := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hc
    have hσY : spectrum K (aeval A₀ G) = (fun k => eval k G) '' spectrum K A₀ :=
      spectrum.map_polynomial_aeval_of_nonempty A₀ G ⟨c, hσX⟩
    have hGc : G.eval c = c := by simp [hGdef, hPc]
    have hGμ : ∀ μ ∈ spectrum K A₀, μ ≠ c → G.eval μ = 1 := by
      intro μ hμ hμc
      have hqμ : q.eval μ = 0 := (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hμ)
      rw [hq, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hqμ
      have hrμ : r.eval μ = 0 := by
        rcases mul_eq_zero.1 hqμ with h | h
        · exact absurd (sub_eq_zero.1 (pow_eq_zero_iff hm.ne' |>.1 h)) hμc
        · exact h
      simp [hGdef, hPdef, hrμ]
    have hsub : ∀ μ ∈ spectrum K (aeval A₀ G), μ = c ∨ μ = 1 := by
      intro μ hμ
      rw [hσY] at hμ
      obtain ⟨ν, hν, rfl⟩ := hμ
      by_cases hνc : ν = c
      · left
        subst hνc
        exact hGc
      · right
        exact hGμ ν hν hνc
    have hcY : c ∈ spectrum K (aeval A₀ G) := by
      rw [hσY]
      exact ⟨c, hσX, hGc⟩
    set Y := aeval A₀ G with hYdef
    have hroots : ∀ μ ∈ Y.charpoly.roots, μ = c ∨ μ = 1 := by
      intro μ hμ
      apply hsub
      exact Matrix.mem_spectrum_iff_isRoot_charpoly.2
        ((mem_roots Y.charpoly_monic.ne_zero).1 hμ)
    refine ⟨Y.charpoly.roots.count c, ?_, ?_, ?_⟩
    · apply Multiset.count_pos.2
      exact (mem_roots Y.charpoly_monic.ne_zero).2
        (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hcY)
    · exact (Multiset.count_le_card _ _).trans
        ((card_roots' _).trans (Matrix.charpoly_natDegree_eq_dim Y).le)
    · rw [hY, Matrix.det_eq_prod_roots_charpoly]
      exact multiset_prod_eq_pow_count c _ hroots

end Block

/-! ### Idempotent splitting off the eigenvalue `1` -/

section Splitting

variable {K : Type*} [Field K]

/-- Splitting an annihilating polynomial with root `1` into its `(X - 1)`-primary part and a
coprime cofactor. -/
theorem exists_unipotent_splitting {Q : K[X]} (hQ : Q ≠ 0) (h1 : Q.IsRoot 1) :
    ∃ (e : ℕ) (R u w : K[X]), Q = (X - C 1) ^ e * R ∧
      u * (X - C 1) ^ e + w * R = 1 ∧ (w * R).eval 1 = 1 := by
  obtain ⟨R, hQR, hR⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ 1
  have he : 0 < Q.rootMultiplicity 1 := (rootMultiplicity_pos hQ).2 h1
  obtain ⟨u, w, huw⟩ :=
    ((irreducible_X_sub_C (1 : K)).coprime_pow_of_not_dvd (Q.rootMultiplicity 1) hR).symm
  refine ⟨Q.rootMultiplicity 1, R, u, w, hQR, huw, ?_⟩
  have := congrArg (eval 1) huw
  simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
    zero_pow he.ne', mul_zero, zero_add, eval_one] at this
  simpa using this

variable {A : Type*} [Ring A] [Algebra K A]

/-- For `a` annihilated by `Q = (X - 1)^e R`, the element `E = (w R)(a)` is idempotent and
`(a - 1)^e E = 0`. -/
theorem splitting_aeval {Q R u w : K[X]} {e : ℕ} (hQR : Q = (X - C 1) ^ e * R)
    (huw : u * (X - C 1) ^ e + w * R = 1) {a : A} (ha : aeval a Q = 0) :
    IsIdempotentElem (aeval a (w * R)) ∧ (a - 1) ^ e * aeval a (w * R) = 0 := by
  have hsub : aeval a (u * (X - C 1) ^ e) = 1 - aeval a (w * R) := by
    rw [eq_sub_iff_add_eq, ← map_add, huw, map_one]
  have hprod : (X - C 1) ^ e * (w * R) = w * Q := by
    rw [hQR]
    ring
  have hzero : aeval a ((X - C 1 : K[X]) ^ e) * aeval a (w * R) = 0 := by
    rw [← map_mul, hprod, map_mul, ha, mul_zero]
  have hpow : aeval a ((X - C 1 : K[X]) ^ e) = (a - 1) ^ e := by
    simp
  refine ⟨?_, by rw [← hpow]; exact hzero⟩
  have h2 : aeval a (w * R) * aeval a (u * (X - C 1) ^ e) = 0 := by
    rw [← map_mul]
    have : w * R * (u * (X - C 1) ^ e) = u * w * Q := by
      rw [hQR]
      ring
    rw [this, map_mul, ha, mul_zero]
  rw [hsub, mul_sub, mul_one, sub_eq_zero] at h2
  exact h2.symm

/-- A matrix over a field whose characteristic-polynomial roots are all roots of `X ^ N - 1`
is annihilated by `(X ^ N - 1) ^ (card n + 1)`. -/
theorem aeval_pow_sub_one_eq_zero [IsAlgClosed K] {n : Type*} [Fintype n] [DecidableEq n]
    (X' : Matrix n n K) (N : ℕ) (h : ∀ μ ∈ X'.charpoly.roots, μ ^ N = 1) :
    aeval X' (((X : K[X]) ^ N - 1) ^ (Fintype.card n + 1)) = 0 := by
  have hsplit := (IsAlgClosed.splits X'.charpoly).eq_prod_roots_of_monic X'.charpoly_monic
  have hdvd : X'.charpoly ∣ ((X : K[X]) ^ N - 1) ^ (Fintype.card n + 1) := by
    rw [hsplit]
    have h1 : (X'.charpoly.roots.map (X - C ·)).prod ∣
        (X'.charpoly.roots.map (fun _ => (X : K[X]) ^ N - 1)).prod := by
      apply Multiset.prod_dvd_prod_of_dvd
      intro μ hμ
      rw [dvd_iff_isRoot]
      simp [h μ hμ]
    refine h1.trans ?_
    rw [Multiset.map_const', Multiset.prod_replicate]
    apply pow_dvd_pow
    exact ((card_roots' _).trans (Matrix.charpoly_natDegree_eq_dim X').le).trans
      (Nat.le_succ _)
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, map_mul, Matrix.aeval_self_charpoly, zero_mul]

end Splitting

end Langlands.GroupScheme.CentralIntersection
