import Langlands.AllFieldBZ.Representation.Category.Contragredient
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Classification.SupercuspidalContragredient

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalContragredient`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalContragredient` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ
universe uF uV

namespace GeneralLinear
open Langlands.GeneralLinear
variable {F : Type uF} [Field F] {n : ℕ}

variable [TopologicalSpace F] [IsTopologicalGroup (GeneralLinear n F)]

namespace SupercuspidalRep
open Langlands.GeneralLinear.SupercuspidalRep
end SupercuspidalRep
namespace SupercuspidalClass
open Langlands.GeneralLinear.SupercuspidalClass
end SupercuspidalClass
end GeneralLinear
namespace LocalFieldPackage
namespace TopologicalData
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- The proposition target `GeneralLinear.SupercuspidalContragredientStatement`
gives the closure hypothesis for every p-adic field, realization and rank. -/
theorem supercuspidalContragredientClosed
    (h : Langlands.GeneralLinear.SupercuspidalContragredientStatement_allFieldBZ.{uF, uV}) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    GeneralLinear.SupercuspidalContragredientClosed.{uF, uV} (F := F.Carrier) (n := n) := by
  let _ : TopologicalSpace F.Carrier := T.topology
  let _ := T.generalLinearTopologicalGroup n
  intro A hA
  exact (h F T n _ A.representation A.isSmooth).1.mpr hA

/-- The smooth contragredient of supercuspidal classes for the topology of `T`,
given the proposition target `GeneralLinear.SupercuspidalContragredientStatement`. -/
def supercuspidalClassContragredient
    (h : Langlands.GeneralLinear.SupercuspidalContragredientStatement_allFieldBZ.{uF, uV}) (n : ℕ) :
    letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) →
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  GeneralLinear.SupercuspidalClass.contragredient (Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ F T n)
    (T.supercuspidalContragredientClosed h n)

theorem supercuspidalClassContragredient_involutive
    (h : Langlands.GeneralLinear.SupercuspidalContragredientStatement_allFieldBZ.{uF, uV}) (n : ℕ) :
    Function.Involutive (T.supercuspidalClassContragredient h n) := by
  let _ : TopologicalSpace F.Carrier := T.topology
  let _ := T.generalLinearTopologicalGroup n
  exact GeneralLinear.SupercuspidalClass.contragredient_involutive _ _

end TopologicalData
end LocalFieldPackage
end Langlands.AllFieldBZ
