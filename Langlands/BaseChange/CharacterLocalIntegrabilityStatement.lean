import Langlands.BaseChange.CharacterFunction
import Langlands.JacquetLanglands.CharacterStatements
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.RepresentationTheory.Irreducible

/-!
# Local integrability of characters of `GL_n(F)`

The statement that the character of an irreducible admissible representation of `GL_n(F)`, for
a nonarchimedean local field `F` of characteristic zero, is given by a locally integrable
function that is locally constant on the regular semisimple set (Harish-Chandra 1999,
Theorem 16.3, printed p. 75). Not proved here. It gives the Library's
`Langlands.JacquetLanglands.HasRegularSemisimpleCharacterValues` (lemma
`CharacterLocalIntegrabilityStatement.hasRegularSemisimpleCharacterValues`, proved).
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

/-- For every nonarchimedean local field `F` of characteristic zero and every `n`: the
character of every irreducible admissible representation `ρ` of `GL_n(F)` on a complex vector
space `V : Type uV` is represented by a function `Θ : GL_n(F) → ℂ`, locally integrable for every
Haar measure, that is locally constant near every regular semisimple element (Harish-Chandra
1999, Theorem 16.3, printed p. 75; Henniart–Lemaire 2011, II.1.3, printed p. 57). -/
def CharacterLocalIntegrabilityStatement.{u, uV} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ),
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F) V) (hρ : IsAdmissible ρ), ρ.IsIrreducible →
      ∃ Θ : GeneralLinear n F → ℂ, IsCharacterFunction ρ hρ Θ ∧
        ∀ g : GeneralLinear n F, IsRegularSemisimple g → ∀ᶠ x in nhds g, Θ x = Θ g

/-- Statement 4 gives the existence of character values at regular semisimple elements: the
value of the character function there. -/
theorem CharacterLocalIntegrabilityStatement.hasRegularSemisimpleCharacterValues.{u, uV}
    (h : CharacterLocalIntegrabilityStatement.{u, uV})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ) :
    HasRegularSemisimpleCharacterValues.{u, uV} F n := by
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  intro V _ _ ρ hρ hirr g hg
  obtain ⟨Θ, hΘ, hloc⟩ := h F n ρ hρ hirr
  exact ⟨Θ g, hΘ.hasCharacterValue (hloc g hg)⟩

end Langlands.BaseChange
