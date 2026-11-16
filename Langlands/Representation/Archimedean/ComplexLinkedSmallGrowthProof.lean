import Langlands.Representation.Archimedean.ComplexLinkedSmallGrowthAdjacent
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwap
import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleReduction
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction

/-!
# Small growth in the dual of a linked standard module

`complexLinkedSmallGrowth_of_unlinkedSwap`: `ComplexStandardUnlinkedSwapStatement` implies
`ComplexLinkedSmallGrowthStatement`.

The dual list `ds'` has the same position characters as `ds.map complexCharacterDataInv`. Choose
a linked pair `d, e` of `ds`, in this order, with the fewest characters `mid` between them
(`exists_minimal_linked`); then no character of `mid` is linked with `e`. The Langlands order
makes both integers `p, q` of the linkage positive. In the inverse list, the inverse of `e` can be
moved next to the inverse of `d` by swapping it with the inverses of the characters of `mid`,
none linked with it (`smallGrowth_move`, from the bijective intertwining maps of
`ComplexStandardUnlinkedSwapStatement` and `smallGrowth_of_intertwine`). In the moved list the
characters at positions `i, i + 1` satisfy `χ_{i+1} = χ_i z^p z̄^q`, the adjacent case
`AdjacentGrowth.smallGrowth_adjacent`.
-/

noncomputable section

open scoped Matrix ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.SmallGrowthTools Langlands.Archimedean.LevelFunctions

namespace LinkedSmallGrowth

/-! ## Weights and exponents at each position -/

/-- The weight of the character at each position, `0` past the end. -/
def posWeight : List ComplexCharacterData → ℕ → ℤ
  | [], _ => 0
  | d :: _, 0 => d.weight
  | _ :: ds, k + 1 => posWeight ds k

/-- The exponent of the character at each position, `0` past the end. -/
def posExponent : List ComplexCharacterData → ℕ → ℂ
  | [], _ => 0
  | d :: _, 0 => d.exponent
  | _ :: ds, k + 1 => posExponent ds k

theorem complexPositionCharacter_eq_phase :
    ∀ (ds : List ComplexCharacterData) (k : ℕ) (z : ℂˣ),
      complexPositionCharacter ds k z =
        phase z ^ posWeight ds k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * posExponent ds k)
  | [], _, _ => by simp [complexPositionCharacter, posWeight, posExponent]
  | d :: _, 0, z => d.character_eq z
  | _ :: ds, k + 1, z => complexPositionCharacter_eq_phase ds k z

theorem posWeight_append :
    ∀ (P Q : List ComplexCharacterData) (k : ℕ), posWeight (P ++ Q) (P.length + k) = posWeight Q k
  | [], Q, k => by simp
  | _ :: P, Q, k => by
    rw [List.cons_append, List.length_cons, Nat.add_right_comm]
    exact posWeight_append P Q k

theorem posExponent_append :
    ∀ (P Q : List ComplexCharacterData) (k : ℕ),
      posExponent (P ++ Q) (P.length + k) = posExponent Q k
  | [], Q, k => by simp
  | _ :: P, Q, k => by
    rw [List.cons_append, List.length_cons, Nat.add_right_comm]
    exact posExponent_append P Q k

/-! ## Linkage -/

theorem not_linked_inv {d e : ComplexCharacterData} (h : ¬ IsComplexLinked d e) :
    ¬ IsComplexLinked (complexCharacterDataInv d) (complexCharacterDataInv e) := by
  rintro ⟨p, q, hpq, hp, hq⟩
  refine h ⟨-p, -q, by nlinarith, ?_, ?_⟩
  · simp only [complexCharacterDataInv] at hp
    push_cast at hp ⊢
    linear_combination -hp
  · simp only [complexCharacterDataInv] at hq
    push_cast at hq ⊢
    linear_combination -hq

theorem exists_linked_decomp :
    ∀ ds : List ComplexCharacterData, ¬ IsComplexUnlinked ds →
      ∃ pre d mid e post, ds = pre ++ d :: (mid ++ e :: post) ∧ IsComplexLinked d e
  | [], h => absurd List.Pairwise.nil h
  | x :: l, h => by
    unfold IsComplexUnlinked at h
    rw [List.pairwise_cons] at h
    by_cases hx : ∀ a ∈ l, ¬ IsComplexLinked x a
    · have hl : ¬ IsComplexUnlinked l := fun hl => h ⟨hx, hl⟩
      obtain ⟨pre, d, mid, e, post, he, hde⟩ := exists_linked_decomp l hl
      exact ⟨x :: pre, d, mid, e, post, by rw [he]; rfl, hde⟩
    · push Not at hx
      obtain ⟨y, hy, hxy⟩ := hx
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hy
      exact ⟨[], x, s, y, t, rfl, hxy⟩

/-- **A linked pair with the fewest characters between them.** -/
theorem exists_minimal_linked {ds : List ComplexCharacterData} (h : ¬ IsComplexUnlinked ds) :
    ∃ pre d mid e post, ds = pre ++ d :: (mid ++ e :: post) ∧ IsComplexLinked d e ∧
      ∀ m ∈ mid, ¬ IsComplexLinked m e := by
  classical
  have hex : ∃ k, ∃ pre d mid e post, ds = pre ++ d :: (mid ++ e :: post) ∧
      IsComplexLinked d e ∧ mid.length = k := by
    obtain ⟨pre, d, mid, e, post, he, hde⟩ := exists_linked_decomp ds h
    exact ⟨_, pre, d, mid, e, post, he, hde, rfl⟩
  obtain ⟨pre, d, mid, e, post, he, hde, hk⟩ := Nat.find_spec hex
  refine ⟨pre, d, mid, e, post, he, hde, fun m hm hme => ?_⟩
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hm
  refine Nat.find_min hex (m := t.length) ?_ ⟨pre ++ d :: s, m, t, e, post, ?_, hme, rfl⟩
  · rw [← hk]
    simp only [List.length_append, List.length_cons]
    omega
  · rw [he]
    simp

/-! ## Moving a character along unlinked characters -/

variable (hT5 : ComplexStandardUnlinkedSwapStatement)

include hT5 in
theorem smallGrowth_swap {n : ℕ} (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (hlen : (pre ++ d :: e :: post).length = n)
    (hde : ¬ IsComplexLinked d e)
    (h : SmallGrowth n (complexPositionCharacter (pre ++ e :: d :: post))) :
    SmallGrowth n (complexPositionCharacter (pre ++ d :: e :: post)) := by
  obtain ⟨T, hT, hTi⟩ := hT5 n pre post d e hlen hde
  exact smallGrowth_of_intertwine T hT.1 (fun k f => hTi.map_complexStandardRep k f)
    (fun x f => hTi.map_complexStandardLie x f) h

include hT5 in
theorem smallGrowth_move {n : ℕ} (x : ComplexCharacterData) (Q : List ComplexCharacterData) :
    ∀ (mid P : List ComplexCharacterData), (∀ m ∈ mid, ¬ IsComplexLinked m x) →
      (P ++ x :: (mid ++ Q)).length = n →
      SmallGrowth n (complexPositionCharacter (P ++ x :: (mid ++ Q))) →
      SmallGrowth n (complexPositionCharacter (P ++ (mid ++ x :: Q)))
  | [], P, _, _, h => by simpa using h
  | m :: mid, P, hmid, hlen, h => by
    have h1 : SmallGrowth n (complexPositionCharacter (P ++ m :: x :: (mid ++ Q))) :=
      smallGrowth_swap hT5 P (mid ++ Q) m x (by simp at hlen ⊢; omega)
        (hmid m List.mem_cons_self) (by simpa using h)
    have h2 := smallGrowth_move x Q mid (P ++ [m])
      (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm')) (by simp at hlen ⊢; omega)
      (by simpa using h1)
    simpa using h2

/-! ## The proof -/

include hT5 in
/-- **`ComplexStandardUnlinkedSwapStatement` implies `ComplexLinkedSmallGrowthStatement`.** -/
theorem complexLinkedSmallGrowth_of_unlinkedSwap : ComplexLinkedSmallGrowthStatement := by
  intro n ds ds' hlen hord hlink hχ
  set inv := complexCharacterDataInv
  have hchar : complexPositionCharacter ds' = complexPositionCharacter (ds.map inv) := by
    funext k z
    have h1 := hχ k z
    have h2 := complexPositionCharacter_map_inv_mul ds k z
    calc complexPositionCharacter ds' k z
        = (complexPositionCharacter (ds.map inv) k z * complexPositionCharacter ds k z) *
            complexPositionCharacter ds' k z := by rw [h2, one_mul]
      _ = complexPositionCharacter (ds.map inv) k z *
            (complexPositionCharacter ds k z * complexPositionCharacter ds' k z) := by ring
      _ = complexPositionCharacter (ds.map inv) k z := by rw [h1, mul_one]
  show SmallGrowth n (complexPositionCharacter ds')
  rw [hchar]
  obtain ⟨pre, d, mid, e, post, hds, hde, hmid⟩ := exists_minimal_linked hlink
  -- the Langlands order makes the linkage integers positive
  have hre : e.exponent.re ≤ d.exponent.re := by
    unfold IsComplexLanglandsOrdered at hord
    rw [hds, List.pairwise_append] at hord
    exact (List.pairwise_cons.1 hord.2.1).1 e (by simp)
  obtain ⟨p, q, hpq, hp, hq⟩ := hde
  have hsumC : ((p : ℂ) + q) = 2 * (d.exponent - e.exponent) := by
    linear_combination -hp - hq
  have hreal : ((p : ℝ) + q) = 2 * (d.exponent.re - e.exponent.re) := by
    have := congrArg Complex.re hsumC
    simp at this
    linarith
  have hsum : 0 ≤ p + q := by
    have : (0 : ℝ) ≤ (p : ℝ) + q := by rw [hreal]; linarith
    exact_mod_cast this
  have hp0 : 0 < p := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hq0 : 0 < q := by
    by_contra hcon
    push Not at hcon
    nlinarith
  obtain ⟨pN, rfl⟩ : ∃ pN : ℕ, (pN : ℤ) = p := ⟨p.toNat, Int.toNat_of_nonneg hp0.le⟩
  obtain ⟨qN, rfl⟩ : ∃ qN : ℕ, (qN : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg hq0.le⟩
  -- the moved list
  set P := pre.map inv
  set Q := mid.map inv ++ post.map inv
  set L0 := P ++ inv d :: inv e :: Q
  have hlen0 : L0.length = n := by
    rw [← hlen, hds]
    simp [L0, P, Q]
    omega
  have hw0 : posWeight L0 P.length = -d.weight := posWeight_append P (inv d :: inv e :: Q) 0
  have hw1 : posWeight L0 (P.length + 1) = -e.weight := posWeight_append P (inv d :: inv e :: Q) 1
  have he0 : posExponent L0 P.length = -d.exponent := posExponent_append P (inv d :: inv e :: Q) 0
  have he1 : posExponent L0 (P.length + 1) = -e.exponent := posExponent_append P (inv d :: inv e :: Q) 1
  have hwint : d.weight - e.weight = (pN : ℤ) - qN := by
    have : ((d.weight - e.weight : ℤ) : ℂ) = (((pN : ℤ) - qN : ℤ) : ℂ) := by
      push_cast at hp hq ⊢
      linear_combination hp - hq
    exact_mod_cast this
  have hadj : SmallGrowth n (complexPositionCharacter L0) := by
    refine AdjacentGrowth.smallGrowth_adjacent (posWeight L0) (posExponent L0)
      (complexPositionCharacter_eq_phase L0) P.length (by rw [← hlen0]; simp [L0]) pN qN
      (by omega) (by omega) ?_ ?_
    · rw [hw0, hw1]; omega
    · rw [he0, he1]
      push_cast at hsumC
      linear_combination -hsumC / 2
  have hmid' : ∀ m ∈ mid.map inv, ¬ IsComplexLinked m (inv e) := by
    intro m hm
    obtain ⟨m₀, hm₀, rfl⟩ := List.mem_map.1 hm
    exact not_linked_inv (hmid m₀ hm₀)
  have hmove := smallGrowth_move hT5 (n := n) (inv e) (post.map inv) (mid.map inv) (P ++ [inv d]) hmid'
    (by rw [← hlen0]; simp [L0, Q, P]) (by simpa [L0, Q] using hadj)
  have hlist : (P ++ [inv d]) ++ (mid.map inv ++ inv e :: post.map inv) = ds.map inv := by
    rw [hds]
    simp [P]
  rw [hlist] at hmove
  exact hmove

end LinkedSmallGrowth

/-! ## The reduction statement -/

/-- **Small growth from unlinked swaps.** If for every two unlinked complex characters `d`, `e`
there is a bijective `(𝔤, K)`-intertwining map from the `U(n)`-finite standard module of
`pre ++ e :: d :: post` onto that of `pre ++ d :: e :: post`
(`ComplexStandardUnlinkedSwapStatement`), then the dual of every Langlands-ordered linked complex
standard module contains a nonzero finite-dimensional `U(n)`-stable subspace `E` with
`dim U_d(𝔤) · E ≤ C (d + 1)^{n(n-1)-1}` (`ComplexLinkedSmallGrowthStatement`). -/
def ComplexLinkedSmallGrowthReductionStatement : Prop :=
  ComplexStandardUnlinkedSwapStatement → ComplexLinkedSmallGrowthStatement

/-- Proof of `ComplexLinkedSmallGrowthReductionStatement`. -/
theorem complexLinkedSmallGrowthReduction : ComplexLinkedSmallGrowthReductionStatement :=
  fun hT5 => LinkedSmallGrowth.complexLinkedSmallGrowth_of_unlinkedSwap hT5

end Langlands.Archimedean
