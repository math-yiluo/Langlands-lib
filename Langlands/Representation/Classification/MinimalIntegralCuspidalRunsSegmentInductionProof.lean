import Langlands.Representation.Classification.MinimalIntegralCuspidalRunsSegmentInductionStatement
import Langlands.Representation.Classification.MinimalConsecutiveBlockSegmentInduction
import Langlands.Representation.Parabolic.FlattenedProductInduction
import Langlands.Representation.Classification.SegmentProductConcatenation

/-! Extract actual strong segment factors from a minimal word of supplied runs. -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open GeneralLinear Geometric PadicField.TopologicalData

universe uF uV uG uW

private theorem subrepresentation_of_targetEquiv
    {G : Type uG} [Group G] [TopologicalSpace G]
    {P Q R : SmoothRep.{0, uG, uW} ℂ G}
    (e : Q.representation.Equiv R.representation)
    (h : SmoothRep.IsSubrepresentation P Q) :
    SmoothRep.IsSubrepresentation P R := by
  obtain ⟨j, hj⟩ := h
  refine ⟨SmoothRep.ofHom (e.toIntertwiningMap.comp (SmoothRep.hom j)), ?_⟩
  intro x y hxy
  exact hj (e.toLinearEquiv.injective hxy)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

theorem minimalIntegralCuspidalRunsSegmentInduction :
    MinimalIntegralCuspidalRunsSegmentInduction.{uF,uV} F T := by
  let := T.topology
  intro m hm n hn A r a l hl π hπi hπa hπf hword hmin
  classical
  let Δ : Fin r → Segment.{max uF uV, uF} T := fun i =>
    ⟨⟨m, hm, T.supercuspidalClassRealPowerTwist m
      ((a i - ((l i - 1 : ℕ) : ℤ) : ℤ) : ℝ) A.isoClass⟩, l i, hl i⟩
  have hlen :
      (List.ofFn (fun i => List.ofFn (fun j : Fin (l i) =>
        a i - (j.val : ℤ)))).flatten.length = ∑ i, l i := by
    simp only [List.length_flatten, List.map_ofFn, Function.comp_def, List.length_ofFn, List.sum_ofFn]
  have hsum : ∑ i, (Δ i).degree = n := by
    change ∑ i, l i * m = n
    rw [← Finset.sum_mul, ← hlen]
    exact integralCuspidalJacquetWord_length_mul F T m n A π _ hword
  let B : BlockShape n := T.segmentShape Δ hsum
  let S : BlockRefinement B := fun i => BlockShape.uniform (l i) m hm
  let C : ∀ i : Fin B.length, ∀ j : Fin (S i).length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := (S i).size j) :=
    fun i j => SupercuspidalRep.twist
      (T.determinantPowerCharacter m ((a i - (j.val : ℤ) : ℤ) : ℝ))
      (T.isOpen_ker_determinantPowerCharacter m _)
      (T.ker_determinant_le_ker_determinantPowerCharacter m _) A
  have hlabels (i : Fin B.length) (j : Fin (S i).length) :
      (⟨(S i).size j, (C i j).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF}
          (F := F.Carrier) (n := d)) =
        ⟨m, T.supercuspidalClassRealPowerTwist m
          ((a i - (j.val : ℤ) : ℤ) : ℝ) A.isoClass⟩ := rfl
  let D : ∀ k : Fin (B.flatten S).length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier)
        (n := (B.flatten S).size k) :=
    fun k => C ((B.flattenBlockEquiv S).symm k).1
      ((B.flattenBlockEquiv S).symm k).2
  let f : Fin (B.flatten S).length → ℤ :=
    fun k => a ((B.flattenBlockEquiv S).symm k).1 -
      (((B.flattenBlockEquiv S).symm k).2.val : ℤ)
  have hD (k : Fin (B.flatten S).length) :
      (⟨(B.flatten S).size k, (D k).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF}
          (F := F.Carrier) (n := d)) =
        ⟨m, T.supercuspidalClassRealPowerTwist m (f k : ℝ) A.isoClass⟩ :=
    hlabels ((B.flattenBlockEquiv S).symm k).1
      ((B.flattenBlockEquiv S).symm k).2
  have hf : List.ofFn f = (List.ofFn (fun i =>
      List.ofFn (fun j : Fin (l i) => a i - (j.val : ℤ)))).flatten :=
    FiniteConcatenation.ofFn_finSigmaFinEquiv l (fun i j => a i - (j.val : ℤ))
  have hocc := integralCuspidalJacquetWord_occurrence_of_labeling F T
    m n A (B.flatten S) D f π hD (hf.symm ▸ hword)
  have hDc := CuspidalSupport.glCuspidalTensor p F T n hn (B.flatten S) D
  obtain ⟨j, hj⟩ := CuspidalSupport.exists_inductionInjection_of_cuspidalOccurrence
    F T (B.flatten S) π (FiniteTensor.externalSmoothObject (fun k => (D k).obj))
      hπi hπa hDc.1 hDc.2 hocc
  let E : Representation.Equiv
      (T.normalizedProductInduced (B.flatten S) (fun k => (D k).obj.representation))
      (T.normalizedProductInduced B (fun i =>
        T.normalizedProductInduced (S i) (fun j => (C i j).obj.representation))) :=
    Parabolic.flattenedProductInducedEquiv.{uF, max uF uV} F T B S
      (fun i j => (C i j).obj)
  have hemb : SmoothRep.IsSubrepresentation π
      ((T.normalizedProductInductionFunctor B).obj (fun i =>
        (T.normalizedProductInductionFunctor (S i)).obj (fun j => (C i j).obj))) := by
    exact subrepresentation_of_targetEquiv
      (P := π)
      (Q := (T.normalizedProductInductionFunctor (B.flatten S)).obj
        (fun k => (D k).obj))
      (R := (T.normalizedProductInductionFunctor B).obj (fun i =>
        (T.normalizedProductInductionFunctor (S i)).obj (fun j => (C i j).obj)))
      E ⟨SmoothRep.ofHom j, hj⟩
  obtain ⟨X, hXi, hXa, hXq, hXemb, hXheads⟩ :=
    exists_inducingSegmentHeads_of_minimal_consecutiveBlocks.{uF,uV} F T m hm n hn A
      B S hl C a π hπi hπa hπf hlabels hemb hmin
  refine ⟨hsum, X, hXi, hXa, ?_, hXq, hXemb⟩
  intro i
  obtain ⟨h, hh⟩ := hXheads i
  have he : h = (rfl : (S i).length * m = B.size i) := Subsingleton.elim _ _
  cases he
  exact hh

end Langlands.Classification
