import Langlands.Representation.Exponents.DualJacquetStatement
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly
import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityProof

/-!
# Analytic temperedness of unitary opposite Jacquet class exponents

The unitary scalar character extends to the full Levi center. The published
scalar-layer assembly, applied to the proved upper necessity theorem, then
gives analytic temperedness of the actual subquotient for the supplied Haar
measure. The reverse implication compares central scalar actions.
-/

namespace Langlands

open GeneralLinear

universe uF uV uW

/-- An actual opposite Jacquet class exponent of a tempered irreducible source
is analytically tempered exactly when its prescribed scalar character is unitary. -/
theorem glTemperedJacquetClassExponent :
    GLTemperedJacquetClassExponentStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B
  let := T.leviTopologicalGroup B
  intro Q _ _ μ _ A hi ht S χ hclass hχ
  have : Nontrivial S := by
    let := hclass.1
    exact IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (B.Levi F.Carrier)) S.ρ.asModule
  constructor
  · exact T.norm_blockScalarCharacter_eq_one_of_isTemperedModCenter
      B S.ρ χ hχ μ
  · intro hunit
    let c := T.unitaryCentralCharacterOfBlockScalar B S.ρ χ hclass.2.1.1 hχ hunit
    exact glTemperedOppositeJacquetScalarLayer_of_productLeviNecessity.{uF, uV, uW}
      glProductLeviTemperedExponentNecessity.{uF, uV}
      p F T n hn B A S A.ρ S.ρ hi ht c hclass.2.2 μ

end Langlands
