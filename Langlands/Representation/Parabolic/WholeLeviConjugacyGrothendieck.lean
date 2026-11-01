import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.CuspidalSupport.LeviGrothendieckTransport
import Langlands.Representation.Parabolic.WholeLeviConjugacyProof
import Langlands.Representation.Smooth.JordanHolderGrothendieck

/-! Whole-Levi conjugacy invariance on actual exact finite-length K0. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear SmoothRep CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (hw : ConjugatesLevi (F := F.Carrier) B C w)

/-- Actual normalized induction after inverse whole-Levi conjugation, on the
full exact finite-length smooth Grothendieck group. -/
def normalizedConjugateInductionK0 :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (normalizedInductionK0.{uF, uV} F T C).comp
    (leviTransportK0.{uF, uV} F.Carrier B C w hw).toLinearMap

/-- Whole-Levi conjugation does not change the induced class, for every
virtual class and in every rank. -/
theorem normalizedInductionK0_comp_leviTransport :
    letI := T.topology
    normalizedConjugateInductionK0.{uF, uV} F T B C w hw =
      normalizedInductionK0.{uF, uV} F T B := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  apply SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object ℂ (B.Levi F.Carrier)
  intro A
  let D := (transportFunctor B C w hw).obj A.val
  let I := (T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A.val
  let Q := (T.normalizedParabolicInductionFunctor.{uF, max uF uV} C).obj D
  have hD : D.HasFiniteLength :=
    transportFunctor_preservesFiniteLength F.Carrier B C w hw A.val A.property
  have hI : I.HasFiniteLength :=
    normalizedInductionK0_hasFiniteLength.{uF, uV} F T B A.val A.property
  have hQ : Q.HasFiniteLength :=
    normalizedInductionK0_hasFiniteLength.{uF, uV} F T C D hD
  have hmatch : HaveSameJordanHolderFactors I.obj Q.obj :=
    wholeLeviInductionConjugacy.{uF, max uF uV, max uF uV} F T n B C w hw
      A.val D A.property hD ⟨Representation.Equiv.refl _⟩
  have hclass : GeneralLinear.finiteLengthClass n F.Carrier I hI =
      GeneralLinear.finiteLengthClass n F.Carrier Q hQ :=
    SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_haveSameJordanHolderFactors
      hI hQ hmatch
  change normalizedInductionK0 F T C
      (leviTransportK0 F.Carrier B C w hw (B.finiteLengthClass F.Carrier A.val A.property)) =
    normalizedInductionK0 F T B (B.finiteLengthClass F.Carrier A.val A.property)
  have h0 := leviTransportK0_finiteLengthClass.{uF, uV}
    F.Carrier B C w hw A.val A.property hD
  have h1 := normalizedInductionK0_finiteLengthClass.{uF, uV} F T C D hD hQ
  have h2 := normalizedInductionK0_finiteLengthClass.{uF, uV} F T B A.val A.property hI
  exact (congrArg (normalizedInductionK0.{uF, uV} F T C) h0).trans
    (h1.trans (hclass.symm.trans h2.symm))

end Langlands.Parabolic
