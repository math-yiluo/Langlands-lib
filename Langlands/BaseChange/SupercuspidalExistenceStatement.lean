import Langlands.BaseChange.PseudoCoefficient
import Langlands.Representation.Classification.Supercuspidal
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Existence of supercuspidal representations of `GL_n(F)`

For every nonarchimedean local field `F` and every `n > 0` there is an irreducible
supercuspidal representation of `GL_n(F)` with a central character. Sources: for `n = 1`,
characters of `F^×`; in general Bushnell-Kutzko 1993, Theorem (6.2.2).
This module defines an unproved proposition. See the paired Markdown.
-/

namespace Langlands.BaseChange

universe u uV

/-- **Existence of supercuspidal representations.** For every nonarchimedean local field `F`
and every `n > 0`, there are a complex vector space `V : Type uV`, a representation `π` of
`GL_n(F)` on `V` and a character `χ` of the centre of `GL_n(F)` such that `π` is irreducible,
supercuspidal (in particular admissible) and has central character `χ`. -/
def SupercuspidalExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∃ (V : Type uV) (_ : AddCommGroup V) (_ : Module ℂ V)
      (π : Representation ℂ (GeneralLinear n F) V)
      (χ : Subgroup.center (GeneralLinear n F) →* ℂˣ),
      π.IsIrreducible ∧ GeneralLinear.IsSupercuspidal π ∧ HasCentralCharacterRep π χ

end Langlands.BaseChange
