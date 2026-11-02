import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTypeOfGenericityStatement
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.Classification.SquareIntegrableUnitarityProof
import Langlands.Representation.Category.UniverseLiftPadic
import Langlands.Representation.Whittaker.Transport

/-!
# Full Whittaker type from supplied square-integrable genericity

The genericity input is applied after an actual universe lift, and the result
is transported back to the original action before using the published
genericity-to-Whittaker-type construction.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV

/-- The explicit square-integrable genericity input supplies full standard
Whittaker type on the original irreducible square-integrable action. -/
theorem squareIntegrableWhittakerType_of_genericity :
    SquareIntegrableWhittakerTypeOfGenericityStatement.{uF,uV} := by
  intro p _ F hG ψ n V _ _ π hiπ hsπ
  let := F.canonicalTopologicalData.topology
  have hadm : IsAdmissible π := hsπ.isAdmissible
  have hunit : IsUnitarizable π :=
    glSquareIntegrableUnitarity p F F.canonicalTopologicalData (n + 1)
      (Nat.succ_pos n) V π hiπ hsπ
  let A : SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    SmoothRep.of π hadm.1
  let B : SmoothRep.{0,uF,max uF uV} ℂ
      (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    SmoothRep.universeLift.{uF} A
  have hgenB : Whittaker.IsGeneric ψ n B.representation :=
    hG n B ((isIrreducible_universeLift_iff π).mpr hiπ)
      ((F.canonicalTopologicalData.isSquareIntegrable_universeLift_iff π).mpr hsπ)
      ((isUnitarizable_universeLift_iff π).mpr hunit) ψ
  have hgen : Whittaker.IsGeneric ψ n π :=
    (Whittaker.isGeneric_iff_of_equiv ψ n
      (SmoothRep.universeLiftEquiv.{uF} A)).mpr hgenB
  exact isOfWhittakerType_of_isGeneric F hgen

end Langlands.RankinSelberg
