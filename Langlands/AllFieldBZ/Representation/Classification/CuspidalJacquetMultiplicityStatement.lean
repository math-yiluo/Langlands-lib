import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement

/-!
# All-field port of `Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
open Langlands.CuspidalSupport
universe uF uV uW

namespace CuspidalJacquetMultiplicity
open Langlands.CuspidalJacquetMultiplicity hiding oppositeJacquet
variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ}

/-- The actual opposite coinvariant action with inverse upper full modulus,
transported to the product Levi and bundled with its linear structure. -/
noncomputable def oppositeJacquet (C : GeneralLinear.BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Rep.{uV} ℂ (C.Levi F.Carrier) :=
  let δ := (T.leviModulus C).comp (C.leviEquiv F.Carrier).symm.toMonoidHom
  Rep.of ((Jacquet.normalizedActionOfModulus A.ρ
    (C.oppositeUnipotentSubgroup F.Carrier) (C.leviSubgroup F.Carrier)
    (C.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
    δ⁻¹).comp (C.leviEquiv F.Carrier).toMonoidHom)

end CuspidalJacquetMultiplicity
end Langlands.AllFieldBZ
