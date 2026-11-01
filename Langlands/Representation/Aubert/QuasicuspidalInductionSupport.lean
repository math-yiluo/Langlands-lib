import Langlands.Representation.Aubert.QuasicuspidalInductionTerms
import Langlands.Representation.Aubert.IrreducibleImageAssembly
import Langlands.VirtualRepresentation.PositiveSupport

/-! Support preservation on constituents of actual quasicuspidal induction. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Parabolic SmoothRep CuspidalSupport
open SmoothRep.IrreducibleGrothendieckProof SmoothRep.IrreducibleOperator
open VirtualRepresentation
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every individual induction--Jacquet term is positive on actual
irreducible factor vectors. -/
theorem inductionJacquet_onIrreducibles_effective {n : ℕ} (C : BlockShape n) :
    letI := T.topology
    ∀ c : SmoothRep.IrreducibleIsoClass.{0, uF, max uF uV} ℂ
        (GeneralLinear n F.Carrier),
      onIrreducibles
        ((normalizedInductionK0.{uF, uV} F T C).comp
          (normalizedJacquetK0.{uF, uV} F T C)) (generator c) ∈ effective := by
  let := T.topology
  intro c
  obtain ⟨A, hA, rfl⟩ := SmoothRep.IrreducibleIsoClass.exists_eq c
  change factorMap
    (normalizedInductionK0 F T C
      (normalizedJacquetK0 F T C
        (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier)
          (generator (SmoothRep.irreducibleIsoClass A hA))))) ∈ effective
  rw [realizeIrreducibles_generator_irreducibleIsoClass A hA
    (hasFiniteLength_of_isIrreducible hA)]
  change factorMap (normalizedInductionK0 F T C (normalizedJacquetK0 F T C
    (GeneralLinear.finiteLengthClass n F.Carrier A
      (hasFiniteLength_of_isIrreducible hA)))) ∈ effective
  obtain ⟨hJ, hJac⟩ := normalizedJacquetK0_spec.{uF, uV} F T C A
    (hasFiniteLength_of_isIrreducible hA)
  rw [hJac]
  obtain ⟨hI, hInd⟩ := normalizedInductionK0_spec.{uF, uV} F T C
    ((T.normalizedJacquetFunctor.{uF, max uF uV} C).obj A) hJ
  rw [hInd]
  rw [GeneralLinear.finiteLengthClass, factorMap_ofRepresentation]
  exact compositionFactors_effective
    ⟨(T.normalizedParabolicInductionFunctor.{uF, max uF uV} C).obj
      ((T.normalizedJacquetFunctor.{uF, max uF uV} C).obj A), hI⟩

/-- On every constituent of a positive-rank quasicuspidal induction, the
individual induction--Jacquet terms and their alternating sum have no
composition factors outside that induction's support. -/
def QuasicuspidalInductionSupportStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
    (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
    (hA : A.HasFiniteLength),
    IsLeviQuasicuspidal B A.representation →
    let v := factorMap (normalizedInductionK0.{uF, uV} F T B
      (B.finiteLengthClass F.Carrier A hA))
    (∀ (C : BlockShape n) (c), c ∈ v.support →
      (onIrreducibles
        ((normalizedInductionK0.{uF, uV} F T C).comp
          (normalizedJacquetK0.{uF, uV} F T C)) (generator c)).support ⊆ v.support) ∧
    (∀ c, c ∈ v.support →
      (onIrreducibles (alternatingOperator.{uF, uV} F T n)
        (generator c)).support ⊆ v.support)

set_option maxHeartbeats 6400000 in
/-- Positivity plus the actual scalar-term identity gives support
preservation before taking the signed alternating sum. -/
theorem quasicuspidalInductionSupport :
    QuasicuspidalInductionSupportStatement.{uF, uV} F T := by
  let := T.topology
  intro n hn B A hA hqc
  let x : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
    normalizedInductionK0.{uF, uV} F T B
    (B.finiteLengthClass F.Carrier A hA)
  let v : SmoothRep.IrreducibleLattice.{0, uF, max uF uV} ℂ
      (GeneralLinear n F.Carrier) := factorMap x
  have hv : v ∈ effective := by
    obtain ⟨hI, hInd⟩ := normalizedInductionK0_spec.{uF, uV} F T B A hA
    change factorMap (normalizedInductionK0 F T B
      (B.finiteLengthClass F.Carrier A hA)) ∈ effective
    rw [hInd]
    rw [GeneralLinear.finiteLengthClass, factorMap_ofRepresentation]
    exact compositionFactors_effective
      ⟨(T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A, hI⟩
  have hterms (C : BlockShape n) (c) (hc : c ∈ v.support) :
      (onIrreducibles
        ((normalizedInductionK0.{uF, uV} F T C).comp
          (normalizedJacquetK0.{uF, uV} F T C)) (generator c)).support ⊆ v.support := by
    obtain ⟨r, hr⟩ := quasicuspidalInductionTerms.{uF, uV} F T n hn B C A hA hqc
    apply support_generator_image_subset_of_nonnegative_scalar
      (onIrreducibles
        ((normalizedInductionK0.{uF, uV} F T C).comp
          (normalizedJacquetK0.{uF, uV} F T C))) v hv
      (fun d _ => inductionJacquet_onIrreducibles_effective F T C d) r ?_ c hc
    change onIrreducibles
      ((normalizedInductionK0 F T C).comp (normalizedJacquetK0 F T C))
      (factorMap x) = r • factorMap x
    rw [onIrreducibles_factorMap]
    change factorMap (normalizedInductionK0 F T C (normalizedJacquetK0 F T C x)) =
      r • factorMap x
    rw [show normalizedInductionK0 F T C (normalizedJacquetK0 F T C x) = r • x
      from hr, map_nsmul]
  refine ⟨hterms, ?_⟩
  intro c hc
  classical
  let : Fintype (BlockShape n) := Fintype.ofFinite _
  have hsum : onIrreducibles (alternatingOperator.{uF, uV} F T n) (generator c) =
      ∑ C : BlockShape n, ((-1 : ℤ) ^ (n - C.length)) •
        onIrreducibles
          ((normalizedInductionK0.{uF, uV} F T C).comp
            (normalizedJacquetK0.{uF, uV} F T C)) (generator c) := by
    change factorMap (alternatingOperator F T n
      (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier) (generator c))) = _
    rw [alternatingOperator_apply, map_sum]
    apply Finset.sum_congr rfl
    intro C _
    exact map_zsmul _ _ _
  intro j hj
  by_contra hjv
  have hzero : (onIrreducibles (alternatingOperator.{uF, uV} F T n)
      (generator c)) j = 0 := by
    rw [hsum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro C _
    have hcol : (onIrreducibles
        ((normalizedInductionK0.{uF, uV} F T C).comp
          (normalizedJacquetK0.{uF, uV} F T C)) (generator c)) j = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => hjv (hterms C c hc h))
    simp only [Finsupp.smul_apply, hcol, smul_zero]
  exact (Finsupp.mem_support_iff.mp hj) hzero

end Langlands.Aubert
