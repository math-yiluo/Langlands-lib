import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.Representation.Smooth.SmallRealizationStatement

/-!
# All-field port of `Langlands.Representation.Smooth.SmallRealizationStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Smooth.SmallRealizationStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
universe uF uW uV

/-- An irreducible smooth complex representation of an actual p-adic general
linear group admits an equivalent irreducible smooth realization in any
independently prescribed carrier universe. -/
def PadicIrreducibleSmoothSmallRealizationStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier),
      π.IsIrreducible →
      ∃ σ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
        σ.IsIrreducible ∧ Nonempty (π.representation.Equiv σ.representation)

end Langlands.AllFieldBZ
