import Langlands.TraceFormula.GeneralLinearLocalSelectionTestStatement
import Langlands.Representation.AffineGeneric.SelectionTest

/-!
# The supercuspidal local selection test for `GL_n`

Proof of `GeneralLinearSupercuspidalSelectionTestStatement`. The completion `K_v` of a number
field at a finite place is a nonarchimedean local field of characteristic zero, so the statement
is the instance `F = K_v` of `Langlands.AffineGeneric.exists_supercuspidalSelectionTest`.
-/

noncomputable section

universe u uW

namespace Langlands.TraceFormula

open Langlands.Global

/-- **Supercuspidal selection test** at a finite place of a number field. -/
theorem generalLinearSupercuspidalSelectionTest :
    GeneralLinearSupercuspidalSelectionTestStatement.{u, uW} := by
  intro K _ _ v r
  let : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    (CompletionPadic.topologicalData v).localField
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  exact AffineGeneric.exists_supercuspidalSelectionTest (v.adicCompletion K) r

end Langlands.TraceFormula
