import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Classification.AdjacentCuspidalJacquetInterchangeStatement
import Langlands.Representation.Classification.RepeatedCuspidalTripleJacquetTransferStatement
import Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapProof
import Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge
import Langlands.Representation.Classification.SegmentTensorStabilizerProof
import Langlands.Representation.Classification.Segments
import Mathlib.Data.List.FinRange

/-! # Transport of actual integral cuspidal Jacquet words -/

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

private theorem ofFn_swap_pair {α : Type*} {k : ℕ} (e : Fin k → α)
    (l r : List α) (a b : α) (he : List.ofFn e = l ++ [a, b] ++ r)
    (hj : l.length + 1 < k) :
    List.ofFn (e ∘ Equiv.swap ⟨l.length, by omega⟩ ⟨l.length + 1, hj⟩) =
      l ++ [b, a] ++ r := by
  have hlen : k = l.length + 2 + r.length := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg List.length he
  have hget (i : Fin k) :
      e i = (l ++ [a, b] ++ r)[i.val]'(by simp [← he]) := by
    simp [← he]
  apply List.ext_getElem
  · simp [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · intro i hi hi'
    simp only [List.getElem_ofFn, Function.comp_apply]
    by_cases hia : i = l.length
    · subst i
      rw [Equiv.swap_apply_left, hget]
      simp
    · by_cases hib : i = l.length + 1
      · subst i
        rw [Equiv.swap_apply_right, hget]
        simp
      · rw [Equiv.swap_apply_of_ne_of_ne (by simpa [Fin.ext_iff] using hia)
          (by simpa [Fin.ext_iff] using hib), hget]
        by_cases hil : i < l.length
        · simp [hil]
        · have hir : l.length + 2 ≤ i := by omega
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
          let q := i - l.length - 2
          have hx : i - l.length = q + 1 + 1 := by omega
          simp only [hx, List.getElem_cons_succ]

private theorem ofFn_triple_values {α : Type*} {k : ℕ} (e : Fin k → α)
    (l r : List α) (a b c : α) (he : List.ofFn e = l ++ [a, b, c] ++ r)
    (hj : l.length + 2 < k) :
    e ⟨l.length, by omega⟩ = a ∧
      e ⟨l.length + 1, by omega⟩ = b ∧ e ⟨l.length + 2, hj⟩ = c := by
  have hget (i : Fin k) :
      e i = (l ++ [a, b, c] ++ r)[i.val]'(by simp [← he]) := by
    simp [← he]
  simp [hget]

section

variable {m n : ℕ}
  {A : letI := T.topology
    SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m)}
  {π : letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
  {w : List ℤ}

/-- The rank is the number of blocks times the rank of the fixed twist line. -/
theorem integralCuspidalJacquetWord_rank
    (h : IntegralCuspidalJacquetWord F T m n A π w) :
    n = w.length * m := by
  let := T.topology
  obtain ⟨B, C, e, rfl, hC, _⟩ := h
  rw [List.length_ofFn]
  calc
    n = ∑ i, B.size i := B.sum_eq.symm
    _ = ∑ _i : Fin B.length, m :=
      Finset.sum_congr rfl (fun i _ => congrArg Sigma.fst (hC i))
    _ = B.length * m := by simp

/-- A nonempty realized word has a positive cuspidal rank. -/
theorem integralCuspidalJacquetWord_rank_pos
    (h : IntegralCuspidalJacquetWord F T m n A π w) (hw : w ≠ []) :
    0 < m := by
  let := T.topology
  obtain ⟨B, C, e, rfl, hC, _⟩ := h
  have hlen : 0 < B.length := by
    simpa only [ne_eq, List.ofFn_eq_nil_iff, Nat.pos_iff_ne_zero] using hw
  let i : Fin B.length := ⟨0, hlen⟩
  have hi : B.size i = m := congrArg Sigma.fst (hC i)
  exact hi ▸ B.positive i

/-- The empty word occurs only at rank zero. -/
theorem integralCuspidalJacquetWord_nil_iff
    (h : IntegralCuspidalJacquetWord F T m n A π w) :
    w = [] ↔ n = 0 := by
  let := T.topology
  constructor
  · intro hw
    simpa [hw] using integralCuspidalJacquetWord_rank F T h
  · intro hn
    obtain ⟨B, C, e, rfl, _, _⟩ := h
    have hlen : B.length = 0 := by have := B.length_le; omega
    simp [hlen]

/-- Reindex the original witnesses once actual occurrence for the permuted
tensor and shape has been supplied. -/
theorem integralCuspidalJacquetWord_of_permuted_occurrence
    : letI := T.topology
    ∀ (B : BlockShape n)
    (C : ∀ i : Fin B.length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i))
    (e : Fin B.length → ℤ),
    (∀ i : Fin B.length,
      (⟨B.size i, (C i).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
          ⟨m, T.supercuspidalClassRealPowerTwist m (e i : ℝ) A.isoClass⟩) →
    ∀ (σ : Equiv.Perm (Fin B.length)),
    SmoothRep.IsSubquotient
      (FiniteTensor.externalSmoothObject (fun i => (C (σ i)).obj))
      ((T.normalizedJacquetFunctor (B.permute σ)).obj π) →
    IntegralCuspidalJacquetWord F T m n A π (List.ofFn (e ∘ σ)) ∧
      (List.ofFn (e ∘ σ)).Perm (List.ofFn e) := by
  let := T.topology
  intro B C e hC σ hocc
  exact ⟨⟨B.permute σ, (fun i => C (σ i)), e ∘ σ, rfl,
    (fun i => hC (σ i)), hocc⟩, σ.ofFn_comp_perm e⟩

/-- An actual irreducible commuting adjacent pair gives its swapped word,
conditional on the actual Jacquet interchange proposition. -/
theorem integralCuspidalJacquetWord_of_adjacent_pair
    (hinterchange : AdjacentCuspidalJacquetInterchange.{uF,uV} F T) :
    letI := T.topology
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
    ∀ (B : BlockShape n)
    (C : ∀ i : Fin B.length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i))
    (e : Fin B.length → ℤ),
    (∀ i : Fin B.length,
      (⟨B.size i, (C i).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
          ⟨m, T.supercuspidalClassRealPowerTwist m (e i : ℝ) A.isoClass⟩) →
    ∀ (l r : List ℤ) (x y : ℤ) (hj : l.length + 1 < B.length),
    List.ofFn e = l ++ [x, y] ++ r →
    SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => (C i).obj))
      ((T.normalizedJacquetFunctor B).obj π) →
    let a : Fin B.length := ⟨l.length, by omega⟩
    let b : Fin B.length := ⟨l.length + 1, hj⟩
    ((T.binaryNormalizedProductFunctor (B.size a) (B.size b)).obj
      ((C a).obj, (C b).obj)).IsIrreducible →
    Nonempty ((T.binaryNormalizedProductFunctor (B.size a) (B.size b)).obj
        ((C a).obj, (C b).obj) ≅
      (Derivative.generalLinearRankCast T (Nat.add_comm (B.size b) (B.size a))).obj
        ((T.binaryNormalizedProductFunctor (B.size b) (B.size a)).obj
          ((C b).obj, (C a).obj))) →
    IntegralCuspidalJacquetWord F T m n A π (l ++ [y, x] ++ r) := by
  let := T.topology
  intro hπ hAdm hFL B C e hC l r x y hj he hocc
  dsimp only
  intro hirr hcomm
  have hnew := hinterchange n B π hπ hAdm hFL C hocc l.length hj hirr hcomm
  have hword' := (integralCuspidalJacquetWord_of_permuted_occurrence F T
    B C e hC (B.adjacentSwap l.length hj) hnew).1
  have hswap := ofFn_swap_pair e l r x y he hj
  simpa [BlockShape.adjacentSwap, hswap] using hword'

private theorem integralCuspidalClasses_step
    : letI := T.topology
    ∀ (B : BlockShape n)
    (C : ∀ i : Fin B.length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i))
    (e : Fin B.length → ℤ),
    (∀ i : Fin B.length,
      (⟨B.size i, (C i).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
          ⟨m, T.supercuspidalClassRealPowerTwist m (e i : ℝ) A.isoClass⟩) →
    ∀ i j : Fin B.length, e i = e j + 1 →
      (⟨B.size i, (C i).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
          ⟨B.size j, T.supercuspidalClassRealPowerTwist (B.size j) 1 (C j).isoClass⟩ := by
  let := T.topology
  intro B C e hC i j hij
  have hν := congrArg
    (fun q : Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d) =>
      (⟨q.1, T.supercuspidalClassRealPowerTwist q.1 1 q.2⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)))
    (hC j)
  calc
    _ = ⟨m, T.supercuspidalClassRealPowerTwist m (e i : ℝ) A.isoClass⟩ := hC i
    _ = ⟨m, T.supercuspidalClassRealPowerTwist m 1
        (T.supercuspidalClassRealPowerTwist m (e j : ℝ) A.isoClass)⟩ := by
      rw [T.supercuspidalClassRealPowerTwist_add, hij, Int.cast_add, Int.cast_one, add_comm]
    _ = _ := hν.symm

/-- Positive rank makes integral labels on the fixed line injective. -/
private theorem integralCuspidalClass_injective (hm : 0 < m) :
    letI := T.topology
    Function.Injective (fun k : ℤ =>
      (⟨m, T.supercuspidalClassRealPowerTwist m (k : ℝ) A.isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d))) := by
  let := T.topology
  intro i j hij
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp hij).2
  apply cuspidalDatum_integralTwist_injective F T
    (⟨m, hm, A.isoClass⟩ : PadicField.TopologicalData.CuspidalDatum T)
  simpa only [PadicField.TopologicalData.CuspidalDatum.twist,
    PadicField.TopologicalData.CuspidalDatum.mk.injEq, heq_eq_eq, true_and] using hc

private theorem integralCuspidalClasses_step_iff (hm : 0 < m)
    : letI := T.topology
    ∀ (B : BlockShape n)
    (C : ∀ i : Fin B.length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i))
    (e : Fin B.length → ℤ),
    (∀ i : Fin B.length,
      (⟨B.size i, (C i).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
          ⟨m, T.supercuspidalClassRealPowerTwist m (e i : ℝ) A.isoClass⟩) →
    ∀ i j : Fin B.length,
      ((⟨B.size i, (C i).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
          ⟨B.size j, T.supercuspidalClassRealPowerTwist (B.size j) 1 (C j).isoClass⟩) ↔
        e i = e j + 1 := by
  let := T.topology
  intro B C e hC i j
  constructor
  · intro hij
    apply integralCuspidalClass_injective F T (A := A) hm
    have hν := congrArg
      (fun q : Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d) =>
        (⟨q.1, T.supercuspidalClassRealPowerTwist q.1 1 q.2⟩ :
          Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)))
      (hC j)
    calc
      _ = ⟨B.size i, (C i).isoClass⟩ := (hC i).symm
      _ = _ := hij
      _ = ⟨m, T.supercuspidalClassRealPowerTwist m 1
          (T.supercuspidalClassRealPowerTwist m (e j : ℝ) A.isoClass)⟩ := hν
      _ = _ := by
        simp only [T.supercuspidalClassRealPowerTwist_add, Int.cast_add, Int.cast_one,
          add_comm]
  · exact integralCuspidalClasses_step F T B C e hC i j

private theorem integralCuspidalPair_product
    (hirreducible : TwoSupercuspidalNonadjacentProductIrreducible.{uF, max uF uV} F T) :
    letI := T.topology
    ∀ (k l : ℕ) (_hk : 0 < k) (_hl : 0 < l)
      (C : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := k))
      (D : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := l)),
    k = l →
    (⟨l, D.isoClass⟩ :
      Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) ≠
        ⟨k, T.supercuspidalClassRealPowerTwist k 1 C.isoClass⟩ →
    (⟨k, C.isoClass⟩ :
      Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) ≠
        ⟨l, T.supercuspidalClassRealPowerTwist l 1 D.isoClass⟩ →
    ((T.binaryNormalizedProductFunctor k l).obj (C.obj, D.obj)).IsIrreducible ∧
      Nonempty ((T.binaryNormalizedProductFunctor k l).obj (C.obj, D.obj) ≅
        (Derivative.generalLinearRankCast T (Nat.add_comm l k)).obj
          ((T.binaryNormalizedProductFunctor l k).obj (D.obj, C.obj))) := by
  let := T.topology
  intro k l hk hl C D hkl hDC hCD
  subst l
  have hprod := hirreducible k k hk hk C D hDC hCD
  constructor
  · simpa only [BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks
      F T hk hk] using hprod
  · change Nonempty ((T.binaryNormalizedProductFunctor k k).obj (C.obj, D.obj) ≅
      (T.binaryNormalizedProductFunctor k k).obj (D.obj, C.obj))
    simpa only [BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks
      F T hk hk] using
      irreducibleTwoFactorProductSwap F T k hk C.obj D.obj C.property.1 D.property.1 hprod

/-- Gap interchanges of actual words, conditional on the two actual transfer
and irreducibility propositions. -/
theorem integralCuspidalJacquetWord_unlinked_pair
    (hinterchange : AdjacentCuspidalJacquetInterchange.{uF,uV} F T)
    (hirreducible : TwoSupercuspidalNonadjacentProductIrreducible.{uF, max uF uV} F T) :
    letI := T.topology
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
    ∀ (l r : List ℤ) (x y : ℤ), x ≠ y + 1 → y ≠ x + 1 →
      IntegralCuspidalJacquetWord F T m n A π (l ++ [x, y] ++ r) →
        IntegralCuspidalJacquetWord F T m n A π (l ++ [y, x] ++ r) := by
  let := T.topology
  intro hπ hAdm hFL l r x y hxy hyx hword
  have hm := integralCuspidalJacquetWord_rank_pos F T hword (by simp)
  obtain ⟨B, C, e, hw, hC, hocc⟩ := hword
  have hj : l.length + 1 < B.length := by
    have hlen := congrArg List.length hw
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_ofFn] at hlen
    omega
  let a : Fin B.length := ⟨l.length, by omega⟩
  let b : Fin B.length := ⟨l.length + 1, hj⟩
  have hget (i : Fin B.length) :
      e i = (l ++ [x, y] ++ r)[i.val]'(by simp [hw]) := by simp [hw]
  have ha : e a = x := by simp [a, hget]
  have hb : e b = y := by simp [b, hget]
  have hrank : B.size a = B.size b :=
    (congrArg Sigma.fst (hC a)).trans (congrArg Sigma.fst (hC b)).symm
  have hDC :
      (⟨B.size b, (C b).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) ≠
        ⟨B.size a, T.supercuspidalClassRealPowerTwist (B.size a) 1 (C a).isoClass⟩ := by
    intro h
    have heq := (integralCuspidalClasses_step_iff F T hm B C e hC b a).mp h
    exact hyx (by simpa only [ha, hb] using heq)
  have hCD :
      (⟨B.size a, (C a).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) ≠
        ⟨B.size b, T.supercuspidalClassRealPowerTwist (B.size b) 1 (C b).isoClass⟩ := by
    intro h
    have heq := (integralCuspidalClasses_step_iff F T hm B C e hC a b).mp h
    exact hxy (by simpa only [ha, hb] using heq)
  obtain ⟨hirr, hcomm⟩ := integralCuspidalPair_product F T hirreducible
    (B.size a) (B.size b) (B.positive a) (B.positive b) (C a) (C b) hrank hDC hCD
  exact integralCuspidalJacquetWord_of_adjacent_pair F T hinterchange
    hπ hAdm hFL B C e hC l r x y hj hw.symm hocc hirr hcomm

/-- The actual lower-repeat transfer gives the corresponding word closure. -/
theorem integralCuspidalJacquetWord_lower_repeat
    (htransfer : RepeatedCuspidalTripleJacquetTransfer.{uF,uV} F T) :
    letI := T.topology
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
      ∀ (l r : List ℤ) (b : ℤ),
        IntegralCuspidalJacquetWord F T m n A π (l ++ [b + 1, b, b] ++ r) →
          IntegralCuspidalJacquetWord F T m n A π (l ++ [b, b + 1, b] ++ r) := by
  let := T.topology
  intro hπ hAdm hFL l r b hword
  obtain ⟨B, C, e, hw, hC, hocc⟩ := hword
  have hj : l.length + 2 < B.length := by
    have hlen := congrArg List.length hw
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_ofFn] at hlen
    omega
  obtain ⟨ha, hb, hc⟩ := ofFn_triple_values e l r (b + 1) b b hw.symm hj
  have hstep := integralCuspidalClasses_step F T B C e hC
    ⟨l.length, by omega⟩ ⟨l.length + 1, by omega⟩ (by rw [ha, hb])
  have hsame :
      (⟨B.size ⟨l.length + 2, hj⟩, (C ⟨l.length + 2, hj⟩).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
        ⟨B.size ⟨l.length + 1, by omega⟩, (C ⟨l.length + 1, by omega⟩).isoClass⟩ := by
    rw [hC, hC, hc, hb]
  have hnew := (htransfer n B π C hπ hAdm hFL hocc l.length hj).1 hstep hsame
  have hword' := (integralCuspidalJacquetWord_of_permuted_occurrence F T
    B C e hC (B.adjacentSwap l.length (by omega)) hnew).1
  have hepair : List.ofFn e = l ++ [b + 1, b] ++ (b :: r) := by
    simpa [List.append_assoc] using hw.symm
  have hswap := ofFn_swap_pair e l (b :: r) (b + 1) b hepair (by omega)
  simpa [BlockShape.adjacentSwap, hswap, List.append_assoc] using hword'

/-- The actual upper-repeat transfer preserves its two alternatives at word level. -/
theorem integralCuspidalJacquetWord_upper_repeat
    (htransfer : RepeatedCuspidalTripleJacquetTransfer.{uF,uV} F T) :
    letI := T.topology
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
      ∀ (l r : List ℤ) (b : ℤ),
        IntegralCuspidalJacquetWord F T m n A π (l ++ [b + 1, b, b + 1] ++ r) →
          IntegralCuspidalJacquetWord F T m n A π (l ++ [b + 1, b + 1, b] ++ r) ∨
          IntegralCuspidalJacquetWord F T m n A π (l ++ [b, b + 1, b + 1] ++ r) := by
  let := T.topology
  intro hπ hAdm hFL l r b hword
  obtain ⟨B, C, e, hw, hC, hocc⟩ := hword
  have hj : l.length + 2 < B.length := by
    have hlen := congrArg List.length hw
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_ofFn] at hlen
    omega
  obtain ⟨ha, hb, hc⟩ := ofFn_triple_values e l r (b + 1) b (b + 1) hw.symm hj
  have hstep := integralCuspidalClasses_step F T B C e hC
    ⟨l.length, by omega⟩ ⟨l.length + 1, by omega⟩ (by rw [ha, hb])
  have hsame :
      (⟨B.size ⟨l.length + 2, hj⟩, (C ⟨l.length + 2, hj⟩).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
        ⟨B.size ⟨l.length, by omega⟩, (C ⟨l.length, by omega⟩).isoClass⟩ := by
    rw [hC, hC, hc, ha]
  obtain hnew | hnew :=
    (htransfer n B π C hπ hAdm hFL hocc l.length hj).2 hstep hsame
  · left
    have hword' := (integralCuspidalJacquetWord_of_permuted_occurrence F T
      B C e hC (B.adjacentSwap (l.length + 1) (by omega)) hnew).1
    have hepair : List.ofFn e = (l ++ [b + 1]) ++ [b, b + 1] ++ r := by
      simpa [List.append_assoc] using hw.symm
    have hswap := ofFn_swap_pair e (l ++ [b + 1]) r b (b + 1) hepair (by simpa using hj)
    have hswap' :
        List.ofFn (e ∘ B.adjacentSwap (l.length + 1) (by omega)) =
          l ++ [b + 1, b + 1, b] ++ r := by
      simpa [BlockShape.adjacentSwap, List.append_assoc] using hswap
    rwa [hswap'] at hword'
  · right
    have hword' := (integralCuspidalJacquetWord_of_permuted_occurrence F T
      B C e hC (B.adjacentSwap l.length (by omega)) hnew).1
    have hepair : List.ofFn e = l ++ [b + 1, b] ++ ((b + 1) :: r) := by
      simpa [List.append_assoc] using hw.symm
    have hswap := ofFn_swap_pair e l ((b + 1) :: r) (b + 1) b hepair (by omega)
    simpa [BlockShape.adjacentSwap, hswap, List.append_assoc] using hword'

end

end Langlands.Classification
