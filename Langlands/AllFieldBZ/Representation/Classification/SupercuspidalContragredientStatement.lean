import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.Representation.Classification.SupercuspidalContragredientStatement

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalContragredientStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalContragredientStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear
universe uF uV

/-- For every p-adic field, field realization, rank and smooth complex
representation `ρ` of `GL_n(F)`: the smooth contragredient of `ρ` is
supercuspidal exactly when `ρ` is, and for admissible `ρ` it is irreducible
exactly when `ρ` is. -/
def _root_.Langlands.GeneralLinear.SupercuspidalContragredientStatement_allFieldBZ : Prop :=
  ∀ (F : Langlands.AllFieldBZ.LocalFieldPackage.{uF}) (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsSmooth ρ →
        (IsSupercuspidal (smoothContragredient ρ) ↔ IsSupercuspidal ρ) ∧
        (IsAdmissible ρ →
          (Representation.IsIrreducible (smoothContragredient ρ) ↔
            Representation.IsIrreducible ρ))

end Langlands.AllFieldBZ.GeneralLinear
