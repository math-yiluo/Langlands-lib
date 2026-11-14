import Langlands.AllFieldBZ.Representation.CuspidalSupport.QuasicuspidalStructureStatement
import Langlands.Representation.CuspidalSupport.ConstituentRankZero

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.ConstituentRankZero`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.ConstituentRankZero` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding LeviCuspidalConstituentTheorem LeviQuasicuspidalDecompositionTheorem leviCuspidalConstituent_rankZero
open CategoryTheory
universe uG uF uV

private def _root_.Langlands.CuspidalSupport.trivialGroupHom {G : Type uG} [Group G] [TopologicalSpace G]
    [Subsingleton G] {A D : SmoothRep.{0, uG, uV} ℂ G}
    (f : A →ₗ[ℂ] D) : A ⟶ D :=
  SmoothRep.ofHom {
    toLinearMap := f
    isIntertwining' g := by
      rw [Subsingleton.elim g 1, map_one, map_one]
      rfl }

/-- The parameterized published target also holds for total rank zero. -/
theorem leviCuspidalConstituent_rankZero (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
    (B : GeneralLinear.BlockShape 0) :
    LeviCuspidalConstituentTheorem.{uF, uV} F T B := by
  let := T.topology
  let : IsEmpty (Fin B.length) := ⟨fun i =>
    Fin.elim0 (B.indexEquiv ⟨i, ⟨0, B.positive i⟩⟩)⟩
  let : Subsingleton (B.Levi F.Carrier) := inferInstance
  intro A D _ _ _ h
  exact constituent_of_subsingleton_group h

end Langlands.AllFieldBZ.CuspidalSupport
