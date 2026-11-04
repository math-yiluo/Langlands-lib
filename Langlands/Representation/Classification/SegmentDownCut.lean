import Langlands.Representation.Classification.Segments
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Classification.SegmentProductSplit
import Langlands.Representation.Classification.JuxtaposedRefinementTools

/-! # Consecutive cuts in the actual decreasing cuspidal induction -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentDownCut

open GeneralLinear Geometric Derivative

universe uF uV

variable (a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)

/-- The two consecutive nonempty groups of uniform blocks. -/
def outer : BlockShape ((a + b) * r) :=
  (BlockShape.binary (a * r) (b * r) (Nat.mul_pos ha hr) (Nat.mul_pos hb hr)).rankCast
    (Nat.add_mul a b r).symm

/-- The two uniform refinements keep all original small blocks. -/
def refinement : BlockRefinement (outer a b r ha hb hr) :=
  Fin.cases (BlockShape.uniform a r hr) (fun _ => BlockShape.uniform b r hr)

/-- Consecutive nested labels are the original uniform block labels. -/
def labels : (Σ i : Fin 2, Fin (refinement a b r ha hb hr i).length) ≃ Fin (a + b) :=
  finSigmaFinEquiv.trans (finCongr (by
    rw [Fin.sum_univ_two]
    rfl))

theorem size_eq (q : Σ i : Fin 2, Fin (refinement a b r ha hb hr i).length) :
    (refinement a b r ha hb hr q.1).size q.2 =
      (BlockShape.uniform (a + b) r hr).size (labels a b r ha hb hr q) := by
  rcases q with ⟨i,j⟩
  fin_cases i <;> rfl

private theorem index_val {n : ℕ} (B : BlockShape n) (i : Fin B.length)
    (x : Fin (B.size i)) :
    (B.index i x).val =
      (∑ j : Fin i.val, B.size (Fin.castLE i.isLt.le j)) + x.val := by
  simp only [BlockShape.index, Function.Embedding.coeFn_mk, BlockShape.indexEquiv,
    Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]

@[simp] theorem labels_zero_val (j : Fin a) :
    (labels a b r ha hb hr ⟨(0 : Fin 2),j⟩).val = j.val := by
  change (finSigmaFinEquiv (⟨(0 : Fin 2),j⟩ :
    Σ i : Fin 2, Fin (Fin.cases a (fun _ => b) i))).val = j.val
  simp [finSigmaFinEquiv_apply]

@[simp] theorem labels_one_val (j : Fin b) :
    (labels a b r ha hb hr ⟨(1 : Fin 2),j⟩).val = a + j.val := by
  change (finSigmaFinEquiv (⟨(1 : Fin 2),j⟩ :
    Σ i : Fin 2, Fin (Fin.cases a (fun _ => b) i))).val = a + j.val
  simp [finSigmaFinEquiv_apply]

@[simp] theorem labels_zero (j : Fin a) :
    labels a b r ha hb hr ⟨(0 : Fin 2),j⟩ = Fin.castAdd b j :=
  Fin.ext (labels_zero_val a b r ha hb hr j)

@[simp] theorem labels_one (j : Fin b) :
    labels a b r ha hb hr ⟨(1 : Fin 2),j⟩ = Fin.natAdd a j :=
  Fin.ext (labels_one_val a b r ha hb hr j)

theorem coordinates (i : Fin 2) (j : Fin (refinement a b r ha hb hr i).length)
    (x : Fin ((refinement a b r ha hb hr i).size j)) :
    (outer a b r ha hb hr).index i ((refinement a b r ha hb hr i).index j x) =
      (BlockShape.uniform (a + b) r hr).index (labels a b r ha hb hr ⟨i,j⟩)
        (Fin.cast (size_eq a b r ha hb hr ⟨i,j⟩) x) := by
  fin_cases i <;> apply Fin.ext
  all_goals
    rw [index_val, index_val, index_val]
    simp only [Fin.val_cast]
  · change (∑ t : Fin 0, (outer a b r ha hb hr).size (Fin.castLE (by decide : 0 ≤ 2) t)) +
        ((∑ _j : Fin j.val, r) + x.val) =
      (∑ _j : Fin (labels a b r ha hb hr ⟨(0 : Fin 2),j⟩).val, r) + x.val
    simp
  · change (∑ j : Fin 1, (BlockShape.binary (a * r) (b * r)
        (Nat.mul_pos ha hr) (Nat.mul_pos hb hr)).size (Fin.castLE (by decide : 1 ≤ 2) j)) +
        ((∑ _j : Fin j.val, r) + x.val) =
      (∑ _j : Fin (labels a b r ha hb hr ⟨(1 : Fin 2),j⟩).val, r) + x.val
    simp [BlockShape.binary, Nat.add_mul, Nat.add_assoc]

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The two induced subfamilies attached to the ordered cut. -/
def nestedFactors
    (X : letI := T.topology
      Fin (a + b) → SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear ((outer a b r ha hb hr).size i) F.Carrier) :=
  letI := T.topology
  fun i => (T.normalizedProductInductionFunctor (refinement a b r ha hb hr i)).obj
    (fun j => (size_eq a b r ha hb hr ⟨i,j⟩).symm ▸
      X (labels a b r ha hb hr ⟨i,j⟩))

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types true in
/-- Regroup the original uniform product along the ordered cut. -/
def uniformNestedCutIso
    (X : letI := T.topology
      Fin (a + b) → SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (BlockShape.uniform (a + b) r hr)).obj X ≅
      (T.normalizedProductInductionFunctor (outer a b r ha hb hr)).obj
        (nestedFactors a b r ha hb hr T X) := by
  letI := T.topology
  let e := Classical.choice (Parabolic.orderedProductRegrouping.{uF,uV} F T ((a + b) * r)
    (BlockShape.uniform (a + b) r hr) (outer a b r ha hb hr)
    (refinement a b r ha hb hr)
    (labels a b r ha hb hr) (size_eq a b r ha hb hr)
    (coordinates a b r ha hb hr) X)
  unfold nestedFactors
  convert! e using 2

set_option maxHeartbeats 400000 in
/-- The outer product is the binary product on the original two ranks. -/
theorem nestedProduct_eq
    (X : letI := T.topology
      Fin (a + b) → SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (outer a b r ha hb hr)).obj
        (nestedFactors a b r ha hb hr T X) =
      (generalLinearRankCast T (Nat.add_mul a b r).symm).obj
        ((T.binaryNormalizedProductFunctor (a * r) (b * r)).obj
          ((T.normalizedProductInductionFunctor (BlockShape.uniform a r hr)).obj
            (fun j => X (Fin.castAdd b j)),
           (T.normalizedProductInductionFunctor (BlockShape.uniform b r hr)).obj
            (fun j => X (Fin.natAdd a j)))) := by
  let := T.topology
  let Y := nestedFactors a b r ha hb hr T X
  have h0 : Y (0 : Fin 2) =
      (T.normalizedProductInductionFunctor (BlockShape.uniform a r hr)).obj
        (fun j => X (Fin.castAdd b j)) := by
    change (T.normalizedProductInductionFunctor (BlockShape.uniform a r hr)).obj
      (fun j => X (labels a b r ha hb hr ⟨(0 : Fin 2),j⟩)) = _
    simp only [labels_zero]
  have h1 : Y (1 : Fin 2) =
      (T.normalizedProductInductionFunctor (BlockShape.uniform b r hr)).obj
        (fun j => X (Fin.natAdd a j)) := by
    change (T.normalizedProductInductionFunctor (BlockShape.uniform b r hr)).obj
      (fun j => X (labels a b r ha hb hr ⟨(1 : Fin 2),j⟩)) = _
    simp only [labels_one]
  rw [SegmentProductSplit.binaryNormalizedProductFunctor_obj_eq T
    (Nat.mul_pos ha hr) (Nat.mul_pos hb hr) _ _ Y h0 h1]
  exact SegmentProductSplit.normalizedProductInductionFunctor_rankCast_obj T _ _ _

/-- Split an arbitrary uniform family into its two consecutive subfamilies. -/
def uniformProductCutIso
    (X : letI := T.topology
      Fin (a + b) → SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (BlockShape.uniform (a + b) r hr)).obj X ≅
      (generalLinearRankCast T (Nat.add_mul a b r).symm).obj
        ((T.binaryNormalizedProductFunctor (a * r) (b * r)).obj
          ((T.normalizedProductInductionFunctor (BlockShape.uniform a r hr)).obj
            (fun j => X (Fin.castAdd b j)),
           (T.normalizedProductInductionFunctor (BlockShape.uniform b r hr)).obj
            (fun j => X (Fin.natAdd a j)))) :=
  letI := T.topology
  uniformNestedCutIso a b r ha hb hr T X ≪≫
    eqToIso (nestedProduct_eq a b r ha hb hr T X)

/-- The first subfamily is the decreasing induction of the shifted base. -/
def decreasingLeftIso
    (A : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (BlockShape.uniform a r hr)).obj
        (fun j => T.segmentFactorsDown A (a + b) hr (Fin.castAdd b j)) ≅
      T.segmentInducedDown (T.segmentFactor A (b : ℝ)) a hr := by
  clear ha hb
  letI := T.topology
  apply (T.normalizedProductInductionFunctor (BlockShape.uniform a r hr)).mapIso
  refine Pi.isoMk fun j => ?_
  change T.segmentFactor A ((a + b - 1 - j.val : ℕ) : ℝ) ≅
    T.segmentFactor (T.segmentFactor A (b : ℝ)) ((a - 1 - j.val : ℕ) : ℝ)
  have h : a + b - 1 - j.val = (a - 1 - j.val) + b := by
    have hj : j.val < a := j.isLt
    omega
  rw [h, Nat.cast_add]
  exact (JuxtaposedShuffle.segmentFactorTwistIso T A (b : ℝ)
    ((a - 1 - j.val : ℕ) : ℝ)).symm

/-- The last subfamily is the decreasing induction on the original base. -/
def decreasingRightIso
    (A : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (BlockShape.uniform b r hr)).obj
        (fun j => T.segmentFactorsDown A (a + b) hr (Fin.natAdd a j)) ≅
      T.segmentInducedDown A b hr := by
  clear ha hb
  letI := T.topology
  apply (T.normalizedProductInductionFunctor (BlockShape.uniform b r hr)).mapIso
  refine Pi.isoMk fun j => ?_
  change T.segmentFactor A ((a + b - 1 - (a + j.val) : ℕ) : ℝ) ≅
    T.segmentFactor A ((b - 1 - j.val : ℕ) : ℝ)
  rw [show a + b - 1 - (a + j.val) = b - 1 - j.val by omega]

/-- Any positive consecutive cut of decreasing induction, retaining the actual iso. -/
def segmentInducedDownCutIso
    (A : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    T.segmentInducedDown A (a + b) hr ≅
      (generalLinearRankCast T (Nat.add_mul a b r).symm).obj
        ((T.binaryNormalizedProductFunctor (a * r) (b * r)).obj
          (T.segmentInducedDown (T.segmentFactor A (b : ℝ)) a hr,
           T.segmentInducedDown A b hr)) :=
  letI := T.topology
  uniformProductCutIso a b r ha hb hr T (T.segmentFactorsDown A (a + b) hr) ≪≫
    (generalLinearRankCast T (Nat.add_mul a b r).symm).mapIso
      ((T.binaryNormalizedProductFunctor (a * r) (b * r)).mapIso
        (Iso.prod (decreasingLeftIso a b r hr T A) (decreasingRightIso a b r hr T A)))

end Langlands.Classification.SegmentDownCut
