import Langlands.Representation.Archimedean.ComplexUnitaryPairedParameters
import Langlands.Representation.Archimedean.ComplexUnitarySwapEigenvalues

/-! Composition of the swaps in disjoint Hermitian pairs. -/

noncomputable section

open scoped Matrix TensorProduct
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexUnitary

attribute [local instance 100] LieRing.ofAssociativeRing

open ComplexBlock

variable {n : ℕ}

/-- The compact-finite vector defined by the base or row-difference test. -/
def testVector (ds : List ComplexCharacterData) (ij : Option (Fin n × Fin n)) : ComplexBlock.KFs n ds :=
  (exists_testVector ds ij).choose

@[simp] theorem testVector_apply (ds : List ComplexCharacterData) (ij : Option (Fin n × Fin n))
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (testVector ds ij : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U) = compactTest ds ij U :=
  (exists_testVector ds ij).choose_spec U

private theorem eq_scaled_testVector {ds : List ComplexCharacterData} (v : ComplexBlock.KFs n ds)
    (ij : Option (Fin n × Fin n)) (c : ℂ)
    (h : ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      (v : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U) = c * compactTest ds ij U) :
    v = c • testVector ds ij := by
  apply Subtype.ext
  apply ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary v.2.1 (c • testVector ds ij).2.1
  intro k hk
  let U : Matrix.unitaryGroup (Fin n) ℂ := ⟨↑k, hk⟩
  rw [← show Unitary.toUnits U = k from Units.ext rfl]
  change _ = c * (testVector ds ij : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U)
  rw [testVector_apply, h]

/-- The real factor for the test in the selected pair, in the normalization of the inducing
characters. -/
def pairRatio (d : ComplexCharacterData) : ℝ := (1 - 2 * d.exponent.re) / (1 + 2 * d.exponent.re)

private theorem pairDifference (d : ComplexCharacterData) :
    d.exponent - (hermitianData d).exponent = ((2 * d.exponent.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, two_mul]

private theorem posWeight_pair_swap (pre post : List ComplexCharacterData) (d : ComplexCharacterData) :
    posWeight (pre ++ d :: hermitianData d :: post) = posWeight (pre ++ hermitianData d :: d :: post) := by
  induction pre with
  | nil =>
    funext i
    rcases i with _ | _ | i <;> simp [posWeight]
  | cons e pre ih =>
    funext i
    cases i with
    | zero => rfl
    | succ i => exact congrFun ih i

/-- A test can be carried through a list of blocks when its rows are either disjoint from a
swapped pair or are precisely the two rows of that pair. The last argument is the product of
the multipliers relative to the base test. -/
inductive BlockTest (ij : Option (Fin n × Fin n)) : ℕ → List ParameterBlock → ℝ → Prop where
  | nil (p : ℕ) : BlockTest ij p [] 1
  | single {p : ℕ} {bs : List ParameterBlock} {r : ℝ} (d : ComplexCharacterData) (hd : d.exponent.re = 0)
      (ht : BlockTest ij (p + 1) bs r) : BlockTest ij p (.single d hd :: bs) r
  | disjoint {p : ℕ} {bs : List ParameterBlock} {r : ℝ} (d : ComplexCharacterData) (hd : 0 < d.exponent.re)
      (ho : ∀ i j, ij = some (i, j) →
        ((i : ℕ) < p ∨ p + 2 ≤ i) ∧ ((j : ℕ) < p ∨ p + 2 ≤ j))
      (ht : BlockTest ij (p + 2) bs r) : BlockTest ij p (.pair d hd :: bs) r
  | selected {p : ℕ} {bs : List ParameterBlock} {r : ℝ} (d : ComplexCharacterData) (hd : 0 < d.exponent.re)
      (hs : ∃ i j, ij = some (i, j) ∧ (i : ℕ) = p ∧ (j : ℕ) = p + 1)
      (ht : BlockTest ij (p + 2) bs r) : BlockTest ij p (.pair d hd :: bs) (pairRatio d * r)

private theorem blockTest_outside (bs : List ParameterBlock) (p : ℕ) (ij : Option (Fin n × Fin n))
    (ho : ∀ i j, ij = some (i, j) →
      ((i : ℕ) < p ∨ p + (bs.flatMap ParameterBlock.data).length ≤ i) ∧
      ((j : ℕ) < p ∨ p + (bs.flatMap ParameterBlock.data).length ≤ j)) :
    BlockTest ij p bs 1 := by
  induction bs generalizing p with
  | nil => exact .nil p
  | cons b bs ih =>
    cases b with
    | single d hd =>
      refine .single d hd (ih (p + 1) fun i j hij => ?_)
      obtain ⟨hi, hj⟩ := ho i j hij
      simp only [List.flatMap_cons, ParameterBlock.data, List.length_append, List.length_cons,
        List.length_nil] at hi hj
      exact ⟨by omega, by omega⟩
    | pair d hd =>
      refine .disjoint d hd (fun i j hij => ?_) (ih (p + 2) fun i j hij => ?_) <;>
        obtain ⟨hi, hj⟩ := ho i j hij <;>
        simp only [List.flatMap_cons, ParameterBlock.data, List.length_append, List.length_cons,
          List.length_nil] at hi hj <;> exact ⟨by omega, by omega⟩

/-- The base test has relative multiplier one through all the swaps. -/
theorem blockTest_base (bs : List ParameterBlock) (p : ℕ) : BlockTest (n := n) none p bs 1 :=
  blockTest_outside bs p none (by simp)

/-- The row-difference test of a specified pair has that pair's relative multiplier. -/
theorem blockTest_selected (before after : List ParameterBlock) (p : ℕ) (d : ComplexCharacterData)
    (hd : 0 < d.exponent.re) (i j : Fin n) (hi : (i : ℕ) = p + (before.flatMap ParameterBlock.data).length)
    (hj : (j : ℕ) = (i : ℕ) + 1) :
    BlockTest (some (i, j)) p (before ++ .pair d hd :: after) (pairRatio d) := by
  induction before generalizing p with
  | nil =>
    have hi' : (i : ℕ) = p := by simpa using hi
    rw [List.nil_append, ← mul_one (pairRatio d)]
    refine .selected d hd ⟨i, j, rfl, hi', by omega⟩ (blockTest_outside after (p + 2) _ ?_)
    intro a b hab
    simp only [Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
  | cons b before ih =>
    cases b with
    | single e he =>
      refine .single e he (ih (p + 1) ?_)
      simp only [List.flatMap_cons, ParameterBlock.data, List.length_append, List.length_cons,
        List.length_nil] at hi
      omega
    | pair e he =>
      simp only [List.flatMap_cons, ParameterBlock.data, List.length_append, List.length_cons,
        List.length_nil] at hi
      refine .disjoint e he (fun a b hab => ?_) (ih (p + 2) (by omega))
      simp only [Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨Or.inr (by omega), Or.inr (by omega)⟩

/-- Compose the swaps from left to right. A test's scalar is a common nonzero factor times
its relative multiplier. -/
theorem exists_blockSwaps (pre : List ComplexCharacterData) (bs : List ParameterBlock)
    (hn : (pre ++ bs.flatMap ParameterBlock.data).length = n) :
    ∃ S : ComplexBlock.KFs n (pre ++ bs.flatMap ParameterBlock.data) →ₗ[ℂ]
        ComplexBlock.KFs n (pre ++ (bs.flatMap ParameterBlock.data).map hermitianData),
      IsComplexStandardIntertwining n (complexStandardRep n (pre ++ (bs.flatMap ParameterBlock.data).map hermitianData))
        (complexStandardLie n (pre ++ (bs.flatMap ParameterBlock.data).map hermitianData))
        (pre ++ bs.flatMap ParameterBlock.data) S ∧
      ∃ c : ℂ, c ≠ 0 ∧ ∀ ij r, BlockTest ij pre.length bs r →
        S (testVector (pre ++ bs.flatMap ParameterBlock.data) ij) =
          (c * (r : ℂ)) • testVector (pre ++ (bs.flatMap ParameterBlock.data).map hermitianData) ij := by
  induction bs generalizing pre with
  | nil =>
    rw [show pre ++ ([] : List ParameterBlock).flatMap ParameterBlock.data = pre from
        List.append_nil pre,
      show pre ++ (([] : List ParameterBlock).flatMap ParameterBlock.data).map hermitianData =
        pre from List.append_nil pre]
    refine ⟨LinearMap.id, isComplexStandardIntertwining_id n pre, 1, one_ne_zero, ?_⟩
    intro ij r ht
    cases ht
    simp
  | cons b bs ih =>
    cases b with
    | single d hd =>
      let tail := bs.flatMap ParameterBlock.data
      have hsrc : pre ++ (.single d hd :: bs).flatMap ParameterBlock.data = pre ++ d :: tail :=
        rfl
      have htgt : pre ++ ((.single d hd :: bs).flatMap ParameterBlock.data).map hermitianData =
          pre ++ d :: tail.map hermitianData := by
        rw [List.flatMap_cons, List.map_append, ParameterBlock.single_map]
        rfl
      rw [hsrc] at hn ⊢
      rw [htgt]
      have h := ih (pre ++ [d]) (by rwa [List.append_assoc])
      rw [show (pre ++ [d]) ++ tail = pre ++ d :: tail from List.append_assoc _ _ _,
        show (pre ++ [d]) ++ tail.map hermitianData = pre ++ d :: tail.map hermitianData from
          List.append_assoc _ _ _] at h
      obtain ⟨S, hS, c, hc, hev⟩ := h
      refine ⟨S, hS, c, hc, fun ij r ht => ?_⟩
      cases ht with
      | single _ _ ht => exact hev ij r (by simpa using ht)
    | pair d hd =>
      let tail := bs.flatMap ParameterBlock.data
      have hsrc : pre ++ (.pair d hd :: bs).flatMap ParameterBlock.data =
          pre ++ d :: hermitianData d :: tail := rfl
      have htgt : pre ++ ((.pair d hd :: bs).flatMap ParameterBlock.data).map hermitianData =
          pre ++ hermitianData d :: d :: tail.map hermitianData := by
        rw [List.flatMap_cons, List.map_append, ParameterBlock.pair_map]
        rfl
      rw [hsrc] at hn ⊢
      rw [htgt]
      let p := pre.length
      have hp : p + 2 ≤ n := by
        simp only [List.length_append, List.length_cons] at hn
        omega
      let D := d.exponent - (hermitianData d).exponent
      have hD : 0 < D.re := by
        simp only [D, Complex.sub_re, hermitianData_re]
        linarith only [hd]
      obtain ⟨S, hS, hSv⟩ := exists_test_swap hn p hp rfl hD (hermitianData_weight d).symm
      have h := ih (pre ++ [hermitianData d, d]) (by
        rw [List.append_assoc]
        change (pre ++ hermitianData d :: d :: tail).length = n
        simpa only [List.length_append, List.length_cons] using hn)
      rw [show (pre ++ [hermitianData d, d]) ++ tail = pre ++ hermitianData d :: d :: tail from
          List.append_assoc _ _ _,
        show (pre ++ [hermitianData d, d]) ++ tail.map hermitianData =
            pre ++ hermitianData d :: d :: tail.map hermitianData from List.append_assoc _ _ _] at h
      obtain ⟨T, hT, c, hc, hTv⟩ := h
      refine ⟨T ∘ₗ S, hS.comp T hT.map_rep (fun X => hT.map_lie (1 ⊗ₜ X)),
        swapScalar d * c, mul_ne_zero (swapScalar_ne_zero d) hc, fun ij r ht => ?_⟩
      have hSv' (hr : ∀ i j, ij = some (i, j) → ij = some (pos p hp 0, pos p hp 1) ∨
          ∀ a, i ≠ pos p hp a ∧ j ≠ pos p hp a) :
          S (testVector (pre ++ d :: hermitianData d :: bs.flatMap ParameterBlock.data) ij) =
            (swapScalar d * swapRatio hp D ij) •
              testVector (pre ++ hermitianData d :: d :: bs.flatMap ParameterBlock.data) ij := by
        apply eq_scaled_testVector
        intro U
        rw [hSv ij hr _ (testVector_apply _ _) U,
          compactTest_eq_of_posWeight_eq (posWeight_pair_swap pre _ d)]
      cases ht with
      | disjoint _ _ ho ht =>
        have hr i j (hij : ij = some (i, j)) (a : Fin 2) : i ≠ pos p hp a ∧ j ≠ pos p hp a := by
          obtain ⟨hi, hj⟩ := ho i j hij
          have ha := a.isLt
          have hv := pos_val p hp a
          exact ⟨fun h => by have := congrArg Fin.val h; omega,
            fun h => by have := congrArg Fin.val h; omega⟩
        have hne : ij ≠ some (pos p hp 0, pos p hp 1) := fun h => (hr _ _ h 0).1 rfl
        rw [LinearMap.comp_apply, hSv' (fun i j h => Or.inr (hr i j h)), swapRatio, ite_eq_right hne,
          mul_one, map_smul, hTv ij _ (by simpa using ht), smul_smul, mul_assoc]
      | selected _ _ hs ht =>
        obtain ⟨i, j, hij, hi, hj⟩ := hs
        have hsel : ij = some (pos p hp 0, pos p hp 1) := by
          rw [hij, show i = pos p hp 0 by apply Fin.ext; simpa [pos_val] using hi,
            show j = pos p hp 1 by apply Fin.ext; simpa [pos_val] using hj]
        have hratio : swapRatio hp D ij = (pairRatio d : ℂ) := by
          rw [swapRatio, ite_eq_left hsel, show D = _ from pairDifference d]
          simp [pairRatio]
        rw [LinearMap.comp_apply, hSv' (fun _ _ _ => Or.inl hsel), hratio, map_smul,
          hTv ij _ (by simpa using ht), smul_smul, Complex.ofReal_mul]
        congr 1
        ring

end Langlands.Archimedean.ComplexUnitary
