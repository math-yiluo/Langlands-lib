import Langlands.Representation.CuspidalSupport.AdjacentMergedTensor
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Derivative.Iteration

/-! Actual adjacent inner inductions from the literal binary product. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.CuspidalSupport

open GeneralLinear Parabolic CategoryTheory Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem productObj_congr {r : ℕ} {C C' : BlockShape r} (h : C = C')
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (A' : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C'.size i) F.Carrier))
    (hA : HEq A A') :
    letI := T.topology
    (T.normalizedProductInductionFunctor C).obj A =
      (T.normalizedProductInductionFunctor C').obj A' := by
  subst h
  cases hA
  rfl

private theorem rankCast_productObj {a b : ℕ} (h : a = b) (C : BlockShape a)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C.size i) F.Carrier)) :
    letI := T.topology
    (generalLinearRankCast T h).obj ((T.normalizedProductInductionFunctor C).obj A) =
      (T.normalizedProductInductionFunctor (C.rankCast h)).obj A := by
  subst h
  rfl

/-- The total rank of a two-block shape is the sum of its two sizes. -/
theorem twoBlockRank {r : ℕ} (C : BlockShape r) (hC : C.length = 2) :
    C.size ⟨0, by omega⟩ + C.size ⟨1, by omega⟩ = r := by
  rcases C with ⟨l,s,hp,hs⟩
  dsimp only at hC
  subst l
  exact (Fin.sum_univ_two s).symm.trans hs

/-- The binary product of the two entries is exactly the normalized product
on an arbitrary two-block shape after the literal total-rank cast. -/
theorem twoBlockProduct_eq {r : ℕ} (C : BlockShape r) (hC : C.length = 2)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C.size i) F.Carrier)) :
    letI := T.topology
    (generalLinearRankCast T (twoBlockRank C hC)).obj
        ((T.binaryNormalizedProductFunctor (C.size ⟨0, by omega⟩)
          (C.size ⟨1, by omega⟩)).obj (A ⟨0, by omega⟩, A ⟨1, by omega⟩)) =
      (T.normalizedProductInductionFunctor C).obj A := by
  let := T.topology
  rcases C with ⟨l,s,hp,hs⟩
  dsimp only at hC
  subst l
  let C : BlockShape r := ⟨2,s,hp,hs⟩
  let h := twoBlockRank C rfl
  let D := BlockShape.binary (s 0) (s 1) (hp 0) (hp 1)
  have hDC : D.rankCast h = C := by
    apply BlockShape.ext_of_size (B₁ := D.rankCast h) (B₂ := C) rfl
    intro i
    fin_cases i <;> rfl
  change (generalLinearRankCast T h).obj
    ((T.binaryNormalizedProductFunctor (s 0) (s 1)).obj (A 0, A 1)) =
      (T.normalizedProductInductionFunctor C).obj A
  rw [T.binaryNormalizedProductFunctor_of_pos (hp 0) (hp 1)]
  change (generalLinearRankCast T h).obj
    ((T.normalizedProductInductionFunctor D).obj
      ((T.binaryPairFamilyFunctor (hp 0) (hp 1)).obj (A 0,A 1))) = _
  rw [rankCast_productObj]
  apply productObj_congr F T hDC
  apply Function.hfunext rfl
  intro i i' hi
  cases hi
  fin_cases i <;> rfl

private theorem rankCast_isIrreducible {a b : ℕ} (h : a = b)
    (X : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
    (hX : letI := T.topology; X.IsIrreducible) :
    letI := T.topology
    ((generalLinearRankCast T h).obj X).IsIrreducible := by
  subst h
  exact hX

/-- On a two-block shape, an irreducible commuting binary product makes the
actual product induction irreducible and identifies it with the reversed product. -/
theorem twoBlockProduct_reverse {r : ℕ} (C : BlockShape r) (hC : C.length = 2)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C.size i) F.Carrier)) :
    letI := T.topology
    let a : Fin C.length := ⟨0, by omega⟩
    let b : Fin C.length := ⟨1, by omega⟩
    ((T.binaryNormalizedProductFunctor (C.size a) (C.size b)).obj
      (A a, A b)).IsIrreducible →
    Nonempty ((T.binaryNormalizedProductFunctor (C.size a) (C.size b)).obj
        (A a, A b) ≅
      (generalLinearRankCast T (Nat.add_comm (C.size b) (C.size a))).obj
        ((T.binaryNormalizedProductFunctor (C.size b) (C.size a)).obj
          (A b, A a))) →
    ((T.normalizedProductInductionFunctor C).obj A).IsIrreducible ∧
      Nonempty ((T.normalizedProductInductionFunctor C).obj A ≅
        (T.normalizedProductInductionFunctor (C.permute Fin.revPerm)).obj
          (fun k => A (Fin.rev k))) := by
  let := T.topology
  rcases C with ⟨l,s,hp,hs⟩
  dsimp only at hC
  subst l
  let C : BlockShape r := ⟨2,s,hp,hs⟩
  dsimp only
  intro hpair ⟨e⟩
  let h := twoBlockRank C rfl
  let hR := twoBlockRank (C.permute Fin.revPerm) rfl
  have E := twoBlockProduct_eq F T C rfl A
  have ER := twoBlockProduct_eq F T (C.permute Fin.revPerm) rfl
    (fun k => A (Fin.rev k))
  change (generalLinearRankCast T h).obj
      ((T.binaryNormalizedProductFunctor (s 0) (s 1)).obj (A 0,A 1)) =
    (T.normalizedProductInductionFunctor C).obj A at E
  change (generalLinearRankCast T hR).obj
      ((T.binaryNormalizedProductFunctor (s 1) (s 0)).obj (A 1,A 0)) =
    (T.normalizedProductInductionFunctor (C.permute Fin.revPerm)).obj
      (fun k => A (Fin.rev k)) at ER
  constructor
  · rw [← E]
    exact rankCast_isIrreducible F T h _ hpair
  · rw [← E, ← ER]
    have ec := (generalLinearRankCast T h).mapIso e
    have hcast :
        (generalLinearRankCast T h).obj
          ((generalLinearRankCast T (Nat.add_comm (s 1) (s 0))).obj
            ((T.binaryNormalizedProductFunctor (s 1) (s 0)).obj (A 1,A 0))) =
        (generalLinearRankCast T hR).obj
          ((T.binaryNormalizedProductFunctor (s 1) (s 0)).obj (A 1,A 0)) := by
      change ((generalLinearRankCast T (Nat.add_comm (s 1) (s 0))) ⋙
        generalLinearRankCast T h).obj _ = _
      rw [generalLinearRankCast_trans]
      rfl
    exact ⟨ec.trans (eqToIso hcast)⟩

/-- Reversing the unique block leaves actual product induction unchanged. -/
theorem oneBlockProduct_reverse_eq {r : ℕ} (C : BlockShape r) (hC : C.length = 1)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor C).obj A =
      (T.normalizedProductInductionFunctor (C.permute Fin.revPerm)).obj
        (fun k => A (Fin.rev k)) := by
  let := T.topology
  have hrev : ∀ k : Fin C.length, Fin.rev k = k := by
    intro k
    apply Fin.ext
    have := k.isLt
    simp only [Fin.val_rev]
    omega
  have hshape : C = C.permute Fin.revPerm := by
    apply BlockShape.ext_of_size (B₁ := C) (B₂ := C.permute Fin.revPerm) rfl
    intro k
    change C.size k = C.size (Fin.rev k)
    rw [hrev]
  apply productObj_congr F T hshape
  apply Function.hfunext rfl
  intro k k' hk
  cases hk
  rw [hrev]

/-- The supplied binary hypotheses give irreducibility and a comparison of the
actual normalized inner inductions at every slot of the adjacent merge. -/
theorem adjacentInnerInductions_irreducible_iso {n : ℕ}
    (B : BlockShape n) (j : ℕ) (hj : j + 1 < B.length)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :
    letI := T.topology
    let a : Fin B.length := ⟨j, by omega⟩
    let b : Fin B.length := ⟨j + 1, hj⟩
    ((T.binaryNormalizedProductFunctor (B.size a) (B.size b)).obj
      ((A a).obj, (A b).obj)).IsIrreducible →
    Nonempty ((T.binaryNormalizedProductFunctor (B.size a) (B.size b)).obj
        ((A a).obj, (A b).obj) ≅
      (generalLinearRankCast T (Nat.add_comm (B.size b) (B.size a))).obj
        ((T.binaryNormalizedProductFunctor (B.size b) (B.size a)).obj
          ((A b).obj, (A a).obj))) →
    ∀ m : Fin (B.adjacentMerge j hj).length,
      ((T.normalizedParabolicInductionFunctor (B.adjacentRefinement j hj m)).obj
        (adjacentInnerTensor F T B j hj A m)).IsIrreducible ∧
      Nonempty
        ((T.normalizedParabolicInductionFunctor (B.adjacentRefinement j hj m)).obj
            (adjacentInnerTensor F T B j hj A m) ≅
          (T.normalizedParabolicInductionFunctor (B.adjacentReverseRefinement j hj m)).obj
            (adjacentReverseTensor F T B j hj A m)) := by
  let := T.topology
  dsimp only
  intro hpair hiso m
  let C := B.adjacentRefinement j hj m
  let X : ∀ k, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C.size k) F.Carrier) :=
    fun k => (A (B.adjacentBlockEquiv j hj ⟨m,k⟩)).obj
  change ((T.normalizedProductInductionFunctor C).obj X).IsIrreducible ∧
    Nonempty ((T.normalizedProductInductionFunctor C).obj X ≅
      (T.normalizedProductInductionFunctor (C.permute Fin.revPerm)).obj
        (fun k => X (Fin.rev k)))
  by_cases hm : m.val = j
  · have hC : C.length = 2 := by
      change (if m.val = j then 2 else 1) = 2
      rw [ite_eq_left hm]
    let k0 : Fin C.length := ⟨0,by omega⟩
    let k1 : Fin C.length := ⟨1,by omega⟩
    have h0 : B.adjacentBlockEquiv j hj ⟨m,k0⟩ = ⟨j,by omega⟩ := by
      apply Fin.ext
      rw [B.adjacentBlockEquiv_val]
      simp [k0, hm]
    have h1 : B.adjacentBlockEquiv j hj ⟨m,k1⟩ = ⟨j+1,hj⟩ := by
      apply Fin.ext
      rw [B.adjacentBlockEquiv_val]
      simp [k1, hm]
    apply twoBlockProduct_reverse F T C hC X
    · change ((T.binaryNormalizedProductFunctor
        (B.size (B.adjacentBlockEquiv j hj ⟨m,k0⟩))
        (B.size (B.adjacentBlockEquiv j hj ⟨m,k1⟩))).obj
          ((A (B.adjacentBlockEquiv j hj ⟨m,k0⟩)).obj,
           (A (B.adjacentBlockEquiv j hj ⟨m,k1⟩)).obj)).IsIrreducible
      rw [h0,h1]
      exact hpair
    · change Nonempty ((T.binaryNormalizedProductFunctor
        (B.size (B.adjacentBlockEquiv j hj ⟨m,k0⟩))
        (B.size (B.adjacentBlockEquiv j hj ⟨m,k1⟩))).obj
          ((A (B.adjacentBlockEquiv j hj ⟨m,k0⟩)).obj,
           (A (B.adjacentBlockEquiv j hj ⟨m,k1⟩)).obj) ≅
        (generalLinearRankCast T (Nat.add_comm
          (B.size (B.adjacentBlockEquiv j hj ⟨m,k1⟩))
          (B.size (B.adjacentBlockEquiv j hj ⟨m,k0⟩)))).obj
          ((T.binaryNormalizedProductFunctor
            (B.size (B.adjacentBlockEquiv j hj ⟨m,k1⟩))
            (B.size (B.adjacentBlockEquiv j hj ⟨m,k0⟩))).obj
              ((A (B.adjacentBlockEquiv j hj ⟨m,k1⟩)).obj,
               (A (B.adjacentBlockEquiv j hj ⟨m,k0⟩)).obj)))
      rw [h0,h1]
      exact hiso
  · have hC : C.length = 1 := B.adjacentRefinement_length_of_ne j hj m hm
    constructor
    · exact isIrreducible_normalizedParabolicInduced_singleBlock T C hC
        (adjacentInnerTensor F T B j hj A m).representation
        (adjacentInnerTensor F T B j hj A m).isSmooth
        (adjacentInnerTensors_cuspidal F T B j hj A m).1.1
    · exact ⟨eqToIso (oneBlockProduct_reverse_eq F T C hC X)⟩

/-- Choose the actual comparison isomorphism for any slot of an adjacent merge,
under precisely the supplied irreducible binary-product hypotheses. -/
def adjacentInnerInductionIso {n : ℕ}
    (B : BlockShape n) (j : ℕ) (hj : j + 1 < B.length)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :
    letI := T.topology
    let a : Fin B.length := ⟨j, by omega⟩
    let b : Fin B.length := ⟨j + 1, hj⟩
    ((T.binaryNormalizedProductFunctor (B.size a) (B.size b)).obj
      ((A a).obj, (A b).obj)).IsIrreducible →
    Nonempty ((T.binaryNormalizedProductFunctor (B.size a) (B.size b)).obj
        ((A a).obj, (A b).obj) ≅
      (generalLinearRankCast T (Nat.add_comm (B.size b) (B.size a))).obj
        ((T.binaryNormalizedProductFunctor (B.size b) (B.size a)).obj
          ((A b).obj, (A a).obj))) →
    ∀ m : Fin (B.adjacentMerge j hj).length,
      (T.normalizedParabolicInductionFunctor (B.adjacentRefinement j hj m)).obj
          (adjacentInnerTensor F T B j hj A m) ≅
        (T.normalizedParabolicInductionFunctor (B.adjacentReverseRefinement j hj m)).obj
          (adjacentReverseTensor F T B j hj A m) := by
  let := T.topology
  dsimp only
  intro hpair hiso m
  exact (adjacentInnerInductions_irreducible_iso F T B j hj A hpair hiso m).2.some

end Langlands.CuspidalSupport
