import Langlands.Representation.Classification.ZeroRankMultisegmentQuotientStatement
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Representation.Classification.TrivialGroupQuotient

/-! The actual empty-product quotient in rank zero. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear

universe uF uV

/-- Every irreducible smooth representation of `GL_0` is a quotient of the
actual empty normalized segment product. -/
theorem zeroRankMultisegmentQuotientExhaustion
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    ZeroRankMultisegmentQuotientExhaustion.{uF, uV} F T := by
  let := T.topology
  let := T.generalLinearTopologicalGroup 0
  intro π hπ
  let d : T.SegmentProductDatum.{max uF uV, uF} 0 :=
    { length := 0
      segments := Fin.elim0
      degree_sum := by simp
      blocks := fun i => Fin.elim0 i }
  refine ⟨d, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · exact isIrreducibleQuotient_of_subsingleton_linearEquiv
      d.induced.representation π.representation hπ
      (rankZeroNormalizedProductLinearEquiv F T d.shape
        (fun i => (d.blocks i).representation))

end Langlands.Classification
