import Langlands.Representation.Smooth.SmallRealizationStatement
import Langlands.AllField.Group.GL.Padic
/-! Independently small realizations of irreducible smooth local-field GL representations.
This module states the existence target; it does not prove a cardinal bound or
construct a realization. -/

namespace Langlands.AllField

universe uF uW uV

/-- An irreducible smooth complex representation of an actual local-field general
linear group admits an equivalent irreducible smooth realization in any
independently prescribed carrier universe. -/
def PadicIrreducibleSmoothSmallRealizationStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ),
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F),
      π.IsIrreducible →
      ∃ σ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F),
        σ.IsIrreducible ∧ Nonempty (π.representation.Equiv σ.representation)

end Langlands.AllField
