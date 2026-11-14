import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalContragredientStatement
import Langlands.Representation.Category.Contragredient

/-!
# All-field port of `Langlands.Representation.Category.Contragredient`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Category.Contragredient` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ
universe uR uG uV uF

namespace SmoothRep
open Langlands.SmoothRep
variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

end SmoothRep
section Complex
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep
open Langlands.SmoothRep
end SmoothRep
namespace IrreducibleAdmissibleRep
open Langlands.IrreducibleAdmissibleRep
end IrreducibleAdmissibleRep
namespace SmoothDualClass
open Langlands.SmoothDualClass
end SmoothDualClass
end Complex
namespace GeneralLinear
open Langlands.GeneralLinear
/-- Compact open subgroups of `GL_n(F)` are cofinal among its open subgroups,
for every p-adic field and topological realization. -/
theorem _root_.Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ (F : Langlands.AllFieldBZ.LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    CompactOpenCofinal (GeneralLinear n F.Carrier) := by
  intro K
  let _ : TopologicalSpace F.Carrier := T.topology
  let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
  exact ⟨L.1, L.2.1, L.2.2⟩

end GeneralLinear
end Langlands.AllFieldBZ
