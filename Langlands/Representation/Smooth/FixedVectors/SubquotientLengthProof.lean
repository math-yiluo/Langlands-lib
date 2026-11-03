import Langlands.Representation.Smooth.FixedVectors.SubquotientLengthStatement
import Langlands.Representation.Smooth.FixedVectors.LengthCriterionProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Compact.SurjectivityProof

/-! Exactness converts fixed vectors in actual subquotients into length bounds. -/

set_option autoImplicit false

noncomputable section

namespace Langlands

universe uG uV

/-- Lift a nonzero fixed quotient vector using compact-open exactness, and
regard its lift as a fixed vector in the ambient representation. -/
theorem compactOpenSubquotientFixedVector :
    CompactOpenSubquotientFixedVectorStatement.{uG, uV} := by
  classical
  intro G _ _ _ V _ _ ρ hρ K hK S T _ hnontrivial
  let ι : T.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := T.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hT : IsSmooth T.toRepresentation :=
    isSmooth_of_injective ι (Submodule.injective_subtype _) hρ
  let q : T.toRepresentation.IntertwiningMap
      (LengthCriterionProof.quotientRep S T) :=
    { toLinearMap := (LengthCriterionProof.lower S T).mkQ
      isIntertwining' := fun _ => rfl }
  have hq : Function.Surjective q :=
    Submodule.mkQ_surjective (LengthCriterionProof.lower S T)
  have hquot : IsSmooth (LengthCriterionProof.quotientRep S T) :=
    isSmooth_of_surjective q hq hT
  let := hnontrivial
  obtain ⟨w, hw⟩ := exists_ne (0 :
    fixedVectors (LengthCriterionProof.quotientRep S T) K.toSubgroup)
  obtain ⟨v, hv⟩ := Compact.fixedVectorSurjectivity G T.toSubmodule
    (T.toSubmodule ⧸ LengthCriterionProof.lower S T)
    T.toRepresentation (LengthCriterionProof.quotientRep S T)
    hT hquot K hK q hq w
  refine ⟨v.val.val, v.val.property, ?_, ?_⟩
  · intro k
    exact congrArg Subtype.val (v.property k)
  · intro hvS
    have hzero : q v.val = 0 :=
      (Submodule.Quotient.mk_eq_zero (LengthCriterionProof.lower S T)).mpr hvS
    apply hw
    apply Subtype.ext
    have hval := congrArg Subtype.val hv
    exact hval.symm.trans hzero

/-- Each strict subquotient supplies a direct fixed-vector witness, so the
ambient fixed dimension bounds actual composition length. -/
theorem compactOpenSubquotientLength :
    CompactOpenSubquotientLengthStatement.{uG, uV} := by
  intro G _ _ _ V _ _ ρ hρ K hK _ hdetect
  apply fixedVectorsStrictInclusionLength ℂ G V ρ K.toSubgroup
  intro S T hST
  exact compactOpenSubquotientFixedVector G V ρ hρ K hK S T hST
    (hdetect S T hST)

/-- The compact-open exactness bridge and its actual length consequence. -/
theorem compactOpenSubquotientLengthReduction :
    CompactOpenSubquotientLengthReductionStatement.{uG, uV} :=
  ⟨compactOpenSubquotientFixedVector, compactOpenSubquotientLength⟩

end Langlands
