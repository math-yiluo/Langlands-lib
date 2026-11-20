import Langlands.Representation.Archimedean.RealDiscreteSeparatedSource
import Langlands.Representation.Archimedean.RealDiscreteComplexFrame

/-!
# Relations between the frame vectors of the separated discrete-series case

The target of the presentation is the list `cs, D_d, …, D_1` (`tgtList`): the characters `cs`
in the first `a = |cs|` coordinates and the plane of the block `D_{d-P}` in the coordinates
`a + 2P` (`z`-column) and `a + 2P + 1` (`z̄`-column). With the complex frame `frameU n a` and
the row sets `rowSet`, this module shows that for every family of column sets `D` there is a
constant `c` with `(L u_D)(1) = c (L u_{D₀})(1)` for every `O(n)`-equivariant `L`, where `D₀` is
the family `tgtSet ∅` (`exists_frame_rel`). The cases are:

* a column set of the wrong size: `u_D = 0`;
* a plane whose rotation weight is at most `|m|` in absolute value: `(L u_D)(1) = 0`;
* a character column hit a number of times of the wrong parity: `(L u_D)(1) = 0`;
* otherwise `D` is tight, hence equal to a family `tgtSet S` (tightness), and a chain of plane
  flips relates `tgtSet S` to `tgtSet ∅`.
-/

noncomputable section

open Finset

open scoped TensorProduct

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealDiscreteSeparated

open MatrixMinor RealDiscretePresentation RealDiscreteShift RealDiscreteTightness RealDiscreteFrame
  RealDiscreteScalar RealTiedMinorProduct RealTiedMinorScalar RealDiscreteMinorCyclic

/-! ## The target list -/

/-- The target `cs, D_d, …, D_1` of the presentation. -/
abbrev tgtList (cs : List RealCharacterData) (Ds : List ComplexCharacterData) : List RealBlock :=
  cs.map RealBlock.character ++ Ds.reverse.map RealBlock.induced

theorem realRank_map_induced :
    ∀ Es : List ComplexCharacterData, realRank (Es.map RealBlock.induced) = 2 * Es.length
  | [] => rfl
  | e :: Es => by
      rw [List.map_cons, realRank_cons, realRank_map_induced Es, List.length_cons]
      simp only [RealBlock.rank]
      ring

theorem realRank_tgtList (cs : List RealCharacterData) (Ds : List ComplexCharacterData) :
    realRank (tgtList cs Ds) = cs.length + 2 * Ds.length := by
  rw [tgtList, Langlands.LocalFactor.Archimedean.realRank_append, realRank_map_character,
    realRank_map_induced, List.length_reverse]

theorem realInducedBlockAt_map_character_append (rest : List RealBlock) :
    ∀ (cs : List RealCharacterData) (p : ℕ),
      realInducedBlockAt (cs.map RealBlock.character ++ rest) (cs.length + p) =
        realInducedBlockAt rest p
  | [], p => by simp
  | c :: cs, p => by
      rw [List.map_cons, List.cons_append, List.length_cons, Nat.add_right_comm]
      simp only [realInducedBlockAt]
      exact realInducedBlockAt_map_character_append rest cs p

theorem realInducedBlockAt_map_induced :
    ∀ (Es : List ComplexCharacterData) (P : ℕ) (hP : P < Es.length),
      realInducedBlockAt (Es.map RealBlock.induced) (2 * P) = some (Es[P]'hP)
  | [], _, hP => by simp at hP
  | e :: Es, 0, _ => by simp [realInducedBlockAt]
  | e :: Es, P + 1, hP => by
      rw [show 2 * (P + 1) = 2 * P + 2 by ring, List.map_cons]
      simp only [realInducedBlockAt, List.getElem_cons_succ]
      exact realInducedBlockAt_map_induced Es P (by simpa using hP)

theorem realInducedBlockAt_tgtList {cs : List RealCharacterData} {Ds : List ComplexCharacterData}
    {P : ℕ} (hP : P < Ds.length) :
    realInducedBlockAt (tgtList cs Ds) (cs.length + 2 * P) =
      some (Ds.reverse[P]'(by simpa using hP)) := by
  rw [tgtList, realInducedBlockAt_map_character_append,
    realInducedBlockAt_map_induced _ P (by simpa using hP)]

theorem realPositionCharacter_map_character_append (rest : List RealBlock) :
    ∀ (cs : List RealCharacterData) (l : ℕ), l < cs.length →
      realPositionCharacter (cs.map RealBlock.character ++ rest) l =
        realPositionCharacter (cs.map RealBlock.character) l
  | [], _, h => by simp at h
  | c :: cs, 0, _ => rfl
  | c :: cs, l + 1, h => by
      simp only [List.map_cons, List.cons_append, realPositionCharacter]
      exact realPositionCharacter_map_character_append rest cs l (by simpa using h)

/-! ## The target column sets -/

variable (cs : List RealCharacterData) (Ds : List ComplexCharacterData)

/-- Membership of the column `x` in the `j`-th target column set of the dominance set `S`: the
odd character columns for `j = 0`, and for each plane `P` with `j < k_P` its `z`-column
(`P ∉ S`) or its `z̄`-column (`P ∈ S`). -/
def memb (S : Finset ℕ) (j x : ℕ) : Prop :=
  if x < cs.length then oddAt cs x ∧ j = 0
  else j < kOf Ds ((x - cs.length) / 2) ∧ ((x - cs.length) % 2 = 1 ↔ (x - cs.length) / 2 ∈ S)

instance (S : Finset ℕ) (j x : ℕ) : Decidable (memb cs Ds S j x) := by
  unfold memb
  infer_instance

/-- The number of target column sets containing the column `x`. -/
def cnt (S : Finset ℕ) (x : ℕ) : ℕ :=
  if x < cs.length then (if oddAt cs x then 1 else 0)
  else if ((x - cs.length) % 2 = 1 ↔ (x - cs.length) / 2 ∈ S) then kOf Ds ((x - cs.length) / 2)
  else 0

/-- The target column sets `D'_S`. -/
def tgtSet (n N : ℕ) (S : Finset ℕ) (j : Fin N) : Finset (Fin n) :=
  univ.filter fun x : Fin n => memb cs Ds S j x

/-- The column of a row: the `y`-row of the plane `P` goes to its `z`-column (`P ∉ S`) or its
`z̄`-column (`P ∈ S`), the row of a character to the column of that character. -/
def rowCol (S : Finset ℕ) (i : ℕ) : ℕ :=
  if Ds.length + cs.length ≤ i then
    cs.length + 2 * (i - (Ds.length + cs.length)) +
      (if i - (Ds.length + cs.length) ∈ S then 1 else 0)
  else i - Ds.length

/-- The inverse of `rowCol`. -/
def colRow (x : ℕ) : ℕ :=
  if x < cs.length then x + Ds.length else Ds.length + cs.length + (x - cs.length) / 2

variable {cs Ds}

theorem memb_char {S : Finset ℕ} {j x : ℕ} (hx : x < cs.length) :
    memb cs Ds S j x ↔ oddAt cs x ∧ j = 0 := by
  unfold memb
  rw [ite_eq_left hx]

theorem memb_plane {S : Finset ℕ} {j P b : ℕ} (hb : b < 2) :
    memb cs Ds S j (cs.length + 2 * P + b) ↔ j < kOf Ds P ∧ (b = 1 ↔ P ∈ S) := by
  have h1 : (cs.length + 2 * P + b - cs.length) / 2 = P := by omega
  have h2 : (cs.length + 2 * P + b - cs.length) % 2 = b := by omega
  unfold memb
  rw [ite_eq_right (by omega), h1, h2]

theorem memb_z {S : Finset ℕ} {j P : ℕ} :
    memb cs Ds S j (cs.length + 2 * P) ↔ j < kOf Ds P ∧ P ∉ S := by
  have h := memb_plane (cs := cs) (Ds := Ds) (S := S) (j := j) (P := P) (b := 0) (by norm_num)
  simpa using h

theorem memb_zbar {S : Finset ℕ} {j P : ℕ} :
    memb cs Ds S j (cs.length + 2 * P + 1) ↔ j < kOf Ds P ∧ P ∈ S := by
  have h := memb_plane (cs := cs) (Ds := Ds) (S := S) (j := j) (P := P) (b := 1) (by norm_num)
  simpa using h

theorem memb_iff_lt_cnt {S : Finset ℕ} {j x : ℕ} : memb cs Ds S j x ↔ j < cnt cs Ds S x := by
  unfold memb cnt
  by_cases hx : x < cs.length
  · rw [ite_eq_left hx, ite_eq_left hx]
    by_cases ho : oddAt cs x
    · rw [ite_eq_left ho]
      constructor
      · rintro ⟨-, rfl⟩
        exact Nat.zero_lt_one
      · intro h
        exact ⟨ho, by omega⟩
    · rw [ite_eq_right ho]
      constructor
      · rintro ⟨h, -⟩
        exact absurd h ho
      · intro h
        omega
  · rw [ite_eq_right hx, ite_eq_right hx]
    by_cases hS : ((x - cs.length) % 2 = 1 ↔ (x - cs.length) / 2 ∈ S)
    · rw [ite_eq_left hS]
      exact ⟨fun h => h.1, fun h => ⟨h, hS⟩⟩
    · rw [ite_eq_right hS]
      exact ⟨fun h => absurd h.2 hS, fun h => absurd h (Nat.not_lt_zero _)⟩

variable {n N : ℕ}

theorem mem_tgtSet {S : Finset ℕ} {j : Fin N} {x : Fin n} :
    x ∈ tgtSet cs Ds n N S j ↔ memb cs Ds S j x := by
  simp only [tgtSet, mem_filter, mem_univ, true_and]

theorem mem_rowSet {j : Fin N} {i : Fin n} :
    i ∈ rowSet cs Ds n N j ↔
      (Ds.length + cs.length ≤ (i : ℕ) ∧ (j : ℕ) < kOf Ds (i - (Ds.length + cs.length))) ∨
        ((j : ℕ) = 0 ∧ Ds.length ≤ (i : ℕ) ∧ (i : ℕ) < Ds.length + cs.length ∧
          oddAt cs (i - Ds.length)) := by
  simp only [rowSet, mem_filter, mem_univ, true_and]

theorem colSet_tgtSet (S : Finset ℕ) (x : Fin n) :
    colSet (tgtSet cs Ds n N S) x = seg N (cnt cs Ds S x) := by
  ext j
  rw [mem_colSet, mem_seg, mem_tgtSet]
  exact memb_iff_lt_cnt

theorem cnt_le (hN : ∀ e ∈ Ds, e.weight.natAbs + 1 ≤ N) (hN1 : 1 ≤ N) (S : Finset ℕ) (x : ℕ) :
    cnt cs Ds S x ≤ N := by
  have := kOf_le hN ((x - cs.length) / 2)
  unfold cnt
  split_ifs <;> omega

theorem rowCol_lt (hn : Ds.length + cs.length + Ds.length = n) (S : Finset ℕ) {i : ℕ}
    (hi : i < n) : rowCol cs Ds S i < n := by
  unfold rowCol
  split_ifs <;> omega

theorem colRow_lt (hn : Ds.length + cs.length + Ds.length = n) {x : ℕ} (hx : x < n) :
    colRow cs Ds x < n := by
  unfold colRow
  split_ifs <;> omega

/-- The target column sets have the sizes of the row sets. -/
theorem card_tgtSet (hn : Ds.length + cs.length + Ds.length = n) (S : Finset ℕ) (j : Fin N) :
    (tgtSet cs Ds n N S j).card = (rowSet cs Ds n N j).card := by
  symm
  refine Finset.card_nbij' (fun i : Fin n => ⟨rowCol cs Ds S i, rowCol_lt hn S i.2⟩)
    (fun x : Fin n => ⟨colRow cs Ds x, colRow_lt hn x.2⟩) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_coe, mem_rowSet] at hi
    rw [Finset.mem_coe, mem_tgtSet]
    show memb cs Ds S j (rowCol cs Ds S i)
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · by_cases hS : (i : ℕ) - (Ds.length + cs.length) ∈ S
      · have e : rowCol cs Ds S i = cs.length + 2 * ((i : ℕ) - (Ds.length + cs.length)) + 1 := by
          unfold rowCol
          rw [ite_eq_left h1, ite_eq_left hS]
        rw [e, memb_zbar]
        exact ⟨h2, hS⟩
      · have e : rowCol cs Ds S i = cs.length + 2 * ((i : ℕ) - (Ds.length + cs.length)) := by
          unfold rowCol
          rw [ite_eq_left h1, ite_eq_right hS, add_zero]
        rw [e, memb_z]
        exact ⟨h2, hS⟩
    · have e : rowCol cs Ds S i = (i : ℕ) - Ds.length := by
        unfold rowCol
        rw [ite_eq_right (by omega)]
      rw [e, memb_char (by omega)]
      exact ⟨h4, h1⟩
  · intro x hx
    rw [Finset.mem_coe, mem_tgtSet] at hx
    rw [Finset.mem_coe, mem_rowSet]
    show (Ds.length + cs.length ≤ colRow cs Ds x ∧
        (j : ℕ) < kOf Ds (colRow cs Ds x - (Ds.length + cs.length))) ∨
      ((j : ℕ) = 0 ∧ Ds.length ≤ colRow cs Ds x ∧ colRow cs Ds x < Ds.length + cs.length ∧
        oddAt cs (colRow cs Ds x - Ds.length))
    by_cases hxa : (x : ℕ) < cs.length
    · rw [memb_char hxa] at hx
      have e : colRow cs Ds x = (x : ℕ) + Ds.length := by
        unfold colRow
        rw [ite_eq_left hxa]
      rw [e]
      right
      refine ⟨hx.2, by omega, by omega, ?_⟩
      rw [show (x : ℕ) + Ds.length - Ds.length = x by omega]
      exact hx.1
    · unfold memb at hx
      rw [ite_eq_right hxa] at hx
      have e : colRow cs Ds x = Ds.length + cs.length + ((x : ℕ) - cs.length) / 2 := by
        unfold colRow
        rw [ite_eq_right hxa]
      rw [e]
      left
      refine ⟨by omega, ?_⟩
      rw [show Ds.length + cs.length + ((x : ℕ) - cs.length) / 2 - (Ds.length + cs.length) =
        ((x : ℕ) - cs.length) / 2 by omega]
      exact hx.1
  · intro i hi
    rw [Finset.mem_coe, mem_rowSet] at hi
    apply Fin.ext
    show colRow cs Ds (rowCol cs Ds S i) = i
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · unfold colRow rowCol
      rw [ite_eq_left h1]
      split_ifs <;> omega
    · have e : rowCol cs Ds S i = (i : ℕ) - Ds.length := by
        unfold rowCol
        rw [ite_eq_right (by omega)]
      rw [e]
      unfold colRow
      rw [ite_eq_left (by omega)]
      omega
  · intro x hx
    rw [Finset.mem_coe, mem_tgtSet] at hx
    apply Fin.ext
    show rowCol cs Ds S (colRow cs Ds x) = x
    unfold colRow rowCol
    by_cases hxa : (x : ℕ) < cs.length
    · rw [ite_eq_left hxa, ite_eq_right (by omega)]
      omega
    · unfold memb at hx
      rw [ite_eq_right hxa] at hx
      rw [ite_eq_right hxa, ite_eq_left (by omega)]
      have e : Ds.length + cs.length + ((x : ℕ) - cs.length) / 2 - (Ds.length + cs.length) =
          ((x : ℕ) - cs.length) / 2 := by omega
      rw [e]
      by_cases hS : ((x : ℕ) - cs.length) / 2 ∈ S
      · rw [ite_eq_left hS]
        have := hx.2.mpr hS
        omega
      · rw [ite_eq_right hS]
        have : ¬ (((x : ℕ) - cs.length) % 2 = 1) := fun h => hS (hx.2.mp h)
        omega

/-! ## Tight families -/

/-- The number of column sets of `D` containing the column `x` (`0` past `n`). -/
def colCount (D : Fin N → Finset (Fin n)) (x : ℕ) : ℕ :=
  if h : x < n then (colSet D ⟨x, h⟩).card else 0

theorem colCount_val (D : Fin N → Finset (Fin n)) (x : Fin n) :
    colCount D x = (colSet D x).card := by
  rw [colCount, dite_eq_left x.2]

variable (cs Ds) in
/-- The planes whose `z̄`-column is hit more often than their `z`-column. -/
def domSet (D : Fin N → Finset (Fin n)) : Finset ℕ :=
  (range Ds.length).filter fun P =>
    colCount D (cs.length + 2 * P) < colCount D (cs.length + 2 * P + 1)

/-- **Tight families are target families.** If the column sets of `D` have the sizes of the row
sets, every odd character column is hit, and every plane `P` has one column hit at least `k_P`
times more often than the other, then `D` is the target family of its dominance set. -/
theorem eq_tgtSet_of_tight (hn : Ds.length + cs.length + Ds.length = n)
    (hN : ∀ e ∈ Ds, e.weight.natAbs + 1 ≤ N) (hN1 : 1 ≤ N) {D : Fin N → Finset (Fin n)}
    (hcard : ∀ j, (D j).card = (rowSet cs Ds n N j).card)
    (hodd : ∀ x : Fin n, (x : ℕ) < cs.length → oddAt cs x → 1 ≤ (colSet D x).card)
    (hplane : ∀ P < Ds.length,
      kOf Ds P + colCount D (cs.length + 2 * P) ≤ colCount D (cs.length + 2 * P + 1) ∨
        kOf Ds P + colCount D (cs.length + 2 * P + 1) ≤ colCount D (cs.length + 2 * P)) :
    D = tgtSet cs Ds n N (domSet cs Ds D) := by
  refine eq_of_tight (fun j => by rw [hcard, card_tgtSet hn]) fun x => ?_
  refine ⟨cnt cs Ds (domSet cs Ds D) x, ?_, cnt_le hN hN1 _ _, colSet_tgtSet _ x⟩
  unfold cnt
  by_cases hxa : (x : ℕ) < cs.length
  · rw [ite_eq_left hxa]
    split_ifs with ho
    · exact hodd x hxa ho
    · exact Nat.zero_le _
  · rw [ite_eq_right hxa]
    split_ifs with hS
    · have hP : ((x : ℕ) - cs.length) / 2 < Ds.length := by omega
      have hk := hplane _ hP
      have hk1 := kOf_pos (Ds := Ds) hP
      have hxv := colCount_val D x
      rcases Nat.mod_two_eq_zero_or_one ((x : ℕ) - cs.length) with h0 | h1
      · have hPS : ((x : ℕ) - cs.length) / 2 ∉ domSet cs Ds D := fun h => by
          have := hS.mpr h
          omega
        have hx : (x : ℕ) = cs.length + 2 * (((x : ℕ) - cs.length) / 2) := by omega
        simp only [domSet, mem_filter, mem_range, not_and, not_lt] at hPS
        have := hPS hP
        rw [hx] at hxv
        omega
      · have hPS : ((x : ℕ) - cs.length) / 2 ∈ domSet cs Ds D := hS.mp h1
        have hx : (x : ℕ) = cs.length + 2 * (((x : ℕ) - cs.length) / 2) + 1 := by omega
        simp only [domSet, mem_filter, mem_range] at hPS
        rw [hx] at hxv
        omega
    · exact Nat.zero_le _

/-! ## The rotation weight -/

theorem sum_sum_eq_sum_card (D : Fin N → Finset (Fin n)) (f : Fin n → ℤ) :
    ∑ j, ∑ l ∈ D j, f l = ∑ l, ((colSet D l).card : ℤ) * f l := by
  rw [Finset.sum_comm' (t' := univ) (s' := fun l => colSet D l)
    (fun j l => by simp [mem_colSet])]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]

theorem sum_rotC (D : Fin N → Finset (Fin n)) (p q : Fin n) (hpq : (q : ℕ) = p + 1) :
    ∑ j, ∑ l ∈ D j, rotC (p : ℕ) l = ((colSet D q).card : ℤ) - (colSet D p).card := by
  have hne : p ≠ q := fun h => by
    rw [h] at hpq
    omega
  rw [sum_sum_eq_sum_card, Fintype.sum_eq_add p q hne]
  · rw [show rotC (p : ℕ) p = -1 by simp [rotC], show rotC (p : ℕ) q = 1 by simp [rotC, hpq]]
    ring
  · intro l hl
    have h1 : (l : ℕ) ≠ p := fun h => hl.1 (Fin.ext h)
    have h2 : (l : ℕ) ≠ p + 1 := fun h => hl.2 (Fin.ext (by omega))
    simp only [rotC, ite_eq_right h1, ite_eq_right h2, mul_zero]

/-! ## Sign matrices -/

theorem kmat_flip (q : Fin n) :
    kmat (RealTiedMinorScalar.flip q) = Matrix.diagonal fun l => if l = q then (-1 : ℂ) else 1 := by
  ext i j
  simp only [kmat, RealTiedMinorScalar.flip, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem prod_prod_flip (D : Fin N → Finset (Fin n)) (l : Fin n) :
    ∏ j, ∏ x ∈ D j, (if x = l then (-1 : ℂ) else 1) = (-1) ^ (colSet D l).card := by
  simp only [Finset.prod_ite_eq']
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rfl

/-! ## The four cases -/

variable {ps qs : List RealBlock} {R : Fin N → Finset (Fin n)}

theorem frameVec_eq_zero (hsh : IsMinorShift n ps qs R) (T : KF n ps)
    (U : Matrix (Fin n) (Fin n) ℂ) (D : Fin N → Finset (Fin n)) {j : Fin N}
    (hj : (D j).card ≠ (R j).card) : frameVec hsh T U D = 0 := by
  apply Subtype.ext
  funext g
  rw [frameVec_apply, Finset.prod_eq_zero (mem_univ j) (minor_of_card_ne (Ne.symm hj)), mul_zero]
  rfl

theorem ev_zero {ds : List RealBlock} : ev (0 : KF n ds) = 0 := rfl

/-- **Rotation vanishing at a plane.** -/
theorem ev_eq_zero_of_plane (hn : Ds.length + cs.length + Ds.length = n)
    (hsh : IsMinorShift n ps qs R) {T : KF n ps} (hT : ∀ k, realStandardRep n ps k T = T)
    {L : KF n qs →ₗ[ℂ] KF n (tgtList cs Ds)} (hL : IsKEquivariant L)
    (D : Fin N → Finset (Fin n)) {P : ℕ} (hP : P < Ds.length)
    (hw : |(colCount D (cs.length + 2 * P + 1) : ℤ) - colCount D (cs.length + 2 * P)| ≤
      |(Ds.reverse[P]'(by simpa using hP)).weight|) :
    ev (L (frameVec hsh T (frameU n cs.length) D)) = 0 := by
  have hev : (n - cs.length) % 2 = 0 := by omega
  have hrk : realRank (tgtList cs Ds) = n := by rw [realRank_tgtList]; omega
  let p : Fin n := ⟨cs.length + 2 * P, by omega⟩
  let q : Fin n := ⟨cs.length + 2 * P + 1, by omega⟩
  refine ev_frameVec_eq_zero_of_rotation hrk hsh hT
    (kmat_rot_mul_frameU hev (by omega) (by omega) (by omega)) (realInducedBlockAt_tgtList hP)
    hL D ?_
  rw [show cs.length + 2 * P = (p : ℕ) from rfl, sum_rotC D p q rfl, ← colCount_val,
    ← colCount_val]
  exact hw

/-- **Parity vanishing at a character column.** -/
theorem ev_eq_zero_of_parity (hsh : IsMinorShift n ps qs R) {T : KF n ps}
    (hT : ∀ k, realStandardRep n ps k T = T)
    {L : KF n qs →ₗ[ℂ] KF n (tgtList cs Ds)} (hL : IsKEquivariant L)
    (D : Fin N → Finset (Fin n)) {l : Fin n} (hl : (l : ℕ) < cs.length)
    (hpar : (colSet D l).card % 2 ≠ (cs[(l : ℕ)]'hl).parity.val) :
    ev (L (frameVec hsh T (frameU n cs.length) D)) = 0 := by
  have hk : kmat (RealTiedMinorScalar.flip l) * frameU n cs.length =
      frameU n cs.length * Matrix.diagonal fun x => if x = l then (-1 : ℂ) else 1 := by
    rw [kmat_flip]
    refine diagonal_mul_frameU _ fun i j hj hij => ?_
    have hi : i ≠ l := fun h => by
      rw [h] at hij
      omega
    have hj' : j ≠ l := fun h => by
      rw [h] at hj
      omega
    rw [ite_eq_right hi, ite_eq_right hj']
  have h := ev_frameVec_sign hsh hT hL (flipUnits l) (toUnits_flip l) hk D
  rw [prod_prod_flip, principalSeriesCharacter_flip, ← sign_eq n (tgtList cs Ds) l,
    realPositionCharacter_map_character_append _ _ _ hl,
    RealTiedScalarAssembly.realPositionCharacter_map_character_neg_one cs _ hl,
    neg_one_pow_eq_pow_mod_two (R := ℂ) (n := (colSet D l).card)] at h
  have hε := (cs[(l : ℕ)]'hl).parity.isLt
  set v := ev (L (frameVec hsh T (frameU n cs.length) D))
  rcases Nat.mod_two_eq_zero_or_one (colSet D l).card with h0 | h1
  · rw [h0] at h hpar
    rw [show (cs[(l : ℕ)]'hl).parity.val = 1 by omega] at h
    have h2 : (2 : ℂ) * v = 0 := by linear_combination h
    simpa using h2
  · rw [h1] at h hpar
    rw [show (cs[(l : ℕ)]'hl).parity.val = 0 by omega] at h
    have h2 : (2 : ℂ) * v = 0 := by linear_combination -h
    simpa using h2

/-- **Plane flips.** Swapping the two columns of a plane not in `S` moves the target family of
`S` to that of `insert P S`. -/
theorem tgtSet_insert {S : Finset ℕ} {P : ℕ} (hPS : P ∉ S) {p q : Fin n}
    (hp : (p : ℕ) = cs.length + 2 * P) (hq : (q : ℕ) = cs.length + 2 * P + 1) (j : Fin N) :
    (tgtSet cs Ds n N S j).map (Equiv.swap p q).toEmbedding = tgtSet cs Ds n N (insert P S) j := by
  ext x
  rw [Finset.mem_map_equiv, Equiv.symm_swap, mem_tgtSet, mem_tgtSet]
  by_cases hxp : x = p
  · rw [hxp, Equiv.swap_apply_left, hp, hq, memb_zbar, memb_z]
    simp [hPS]
  · by_cases hxq : x = q
    · rw [hxq, Equiv.swap_apply_right, hp, hq, memb_zbar, memb_z]
      simp [hPS]
    · rw [Equiv.swap_apply_of_ne_of_ne hxp hxq]
      have h1 : (x : ℕ) ≠ cs.length + 2 * P := fun h => hxp (Fin.ext (h.trans hp.symm))
      have h2 : (x : ℕ) ≠ cs.length + 2 * P + 1 := fun h => hxq (Fin.ext (h.trans hq.symm))
      unfold memb
      split_ifs with hxa
      · exact Iff.rfl
      · have h3 : ((x : ℕ) - cs.length) / 2 ≠ P := by omega
        rw [Finset.mem_insert, or_iff_right h3]

theorem not_mem_both {S : Finset ℕ} {P : ℕ} {p q : Fin n}
    (hp : (p : ℕ) = cs.length + 2 * P) (hq : (q : ℕ) = cs.length + 2 * P + 1) (j : Fin N) :
    ¬ (p ∈ tgtSet cs Ds n N S j ∧ q ∈ tgtSet cs Ds n N S j) := by
  rw [mem_tgtSet, mem_tgtSet, hp, hq, memb_z, memb_zbar]
  tauto

/-- **The flip chain.** For every set `S` of planes, the values on the target family of `S`
are multiples of the values on the target family of `∅`. -/
theorem exists_chain (hn : Ds.length + cs.length + Ds.length = n)
    (hsh : IsMinorShift n ps qs R) {T : KF n ps} (hT : ∀ k, realStandardRep n ps k T = T)
    (S : Finset ℕ) (hS : S ⊆ range Ds.length) :
    ∃ c : ℂ, ∀ L : KF n qs →ₗ[ℂ] KF n (tgtList cs Ds), IsKEquivariant L →
      ev (L (frameVec hsh T (frameU n cs.length) (tgtSet cs Ds n N S))) =
        c * ev (L (frameVec hsh T (frameU n cs.length) (tgtSet cs Ds n N ∅))) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun L _ => (one_mul _).symm⟩
  | insert P S hPS ih =>
    obtain ⟨c, hc⟩ := ih ((Finset.subset_insert P S).trans hS)
    have hP : P < Ds.length := mem_range.mp (hS (mem_insert_self P S))
    let p : Fin n := ⟨cs.length + 2 * P, by omega⟩
    let q : Fin n := ⟨cs.length + 2 * P + 1, by omega⟩
    have e : (fun l : Fin n => if l = q then (-1 : ℂ) else 1) =
        fun l : Fin n => if (l : ℕ) = cs.length + 2 * P + 1 then (-1 : ℂ) else 1 := by
      funext l
      simp only [q, Fin.ext_iff]
    have hk : kmat (RealTiedMinorScalar.flip q) * frameU n cs.length =
        (frameU n cs.length).submatrix id (Equiv.swap p q) := by
      rw [kmat_flip, e]
      exact diagonal_flip_mul_frameU (by omega) (by omega) (by omega)
    have hD : ∀ (j : Fin N) (X : Matrix (Fin n) (Fin n) ℂ),
        minor (X.submatrix id (Equiv.swap p q)) (R j) (tgtSet cs Ds n N S j) =
          minor X (R j) (tgtSet cs Ds n N (insert P S) j) := fun j X => by
      rw [minor_submatrix_swap X _ _ rfl (not_mem_both rfl rfl j), tgtSet_insert hPS rfl rfl j]
    refine ⟨principalSeriesCharacter ℝ n (realPositionCharacter (tgtList cs Ds)) (flipUnits q) * c,
      fun L hL => ?_⟩
    rw [ev_frameVec_flip hsh hT hL (flipUnits q) (toUnits_flip q) hk hD, hc L hL, mul_assoc]

/-- **The relations.** For every family `D` of column sets there is a constant `c` with
`(L u_D)(1) = c (L u_{D₀})(1)` for every `O(n)`-equivariant `L`, `D₀ = tgtSet ∅`. -/
theorem exists_frame_rel (hn : Ds.length + cs.length + Ds.length = n)
    (hN : ∀ e ∈ Ds, e.weight.natAbs + 1 ≤ N) (hN1 : 1 ≤ N)
    (hsh : IsMinorShift n ps qs (rowSet cs Ds n N)) {T : KF n ps}
    (hT : ∀ k, realStandardRep n ps k T = T) (D : Fin N → Finset (Fin n)) :
    ∃ c : ℂ, ∀ L : KF n qs →ₗ[ℂ] KF n (tgtList cs Ds), IsKEquivariant L →
      ev (L (frameVec hsh T (frameU n cs.length) D)) =
        c * ev (L (frameVec hsh T (frameU n cs.length) (tgtSet cs Ds n N ∅))) := by
  by_cases h1 : ∀ j, (D j).card = (rowSet cs Ds n N j).card
  swap
  · push Not at h1
    obtain ⟨j, hj⟩ := h1
    refine ⟨0, fun L _ => ?_⟩
    rw [frameVec_eq_zero hsh T _ D hj, map_zero, ev_zero, zero_mul]
  by_cases h2 : ∃ P, ∃ hP : P < Ds.length,
      |(colCount D (cs.length + 2 * P + 1) : ℤ) - colCount D (cs.length + 2 * P)| ≤
        |(Ds.reverse[P]'(by simpa using hP)).weight|
  · obtain ⟨P, hP, hw⟩ := h2
    exact ⟨0, fun L hL => by rw [ev_eq_zero_of_plane hn hsh hT hL D hP hw, zero_mul]⟩
  by_cases h3 : ∃ l : Fin n, ∃ hl : (l : ℕ) < cs.length,
      (colSet D l).card % 2 ≠ (cs[(l : ℕ)]'hl).parity.val
  · obtain ⟨l, hl, hpar⟩ := h3
    exact ⟨0, fun L hL => by rw [ev_eq_zero_of_parity hsh hT hL D hl hpar, zero_mul]⟩
  push Not at h2 h3
  have hD : D = tgtSet cs Ds n N (domSet cs Ds D) := by
    refine eq_tgtSet_of_tight hn hN hN1 h1 (fun x hx ho => ?_) (fun P hP => ?_)
    · have := h3 x hx
      rw [(oddAt_iff cs hx).mp ho] at this
      omega
    · have hw := h2 P hP
      have hk := kOf_eq Ds (P := P) hP
      rw [Int.abs_eq_natAbs (Ds.reverse[P]'(by simpa using hP)).weight] at hw
      rcases le_or_gt (colCount D (cs.length + 2 * P)) (colCount D (cs.length + 2 * P + 1))
        with hle | hlt
      · left
        rw [abs_of_nonneg (by omega)] at hw
        omega
      · right
        rw [abs_of_neg (by omega)] at hw
        omega
  rw [hD]
  exact exists_chain hn hsh hT _ (filter_subset _ _)

end RealDiscreteSeparated

end Langlands.Archimedean
