import Langlands.Group.GL.Padic
import Langlands.Representation.Category.Basic
import Mathlib.Basic.Complex.Basic

/-! Independently small realizations of irreducible smooth p-adic GL representations.
This module states the existence target; it does not prove a cardinal bound or
construct a realization. -/

namespace Langlands

universe uF uW uV

/-- An irreducible smooth complex representation of an actual p-adic general
linear group admits an equivalent irreducible smooth realization in any
independently prescribed carrier universe. -/
def PadicIrreducibleSmoothSmallRealizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier),
      π.IsIrreducible →
      ∃ σ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
        σ.IsIrreducible ∧ Nonempty (π.representation.Equiv σ.representation)

end Langlands
