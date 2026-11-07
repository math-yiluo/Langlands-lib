import Langlands.Automorphic.OperatorRealization

/-! # Central characters of irreducible operator realizations

Borel–Jacquet (1979), 4.3(iv) and 4.6: automorphic forms are finite under the center of
`G(𝔸)`, and irreducible automorphic representations are admissible, so by Schur's lemma
the center acts on them through a character. For an actual irreducible operator
realization of `GL_n` over a number field, this says that exactly one continuous
character of the idele class group is a central character of the realization. Proposition
definition only.
-/

noncomputable section

universe u

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global NumberField

/-- Borel–Jacquet (1979), 4.3(iv) and 4.6, with Schur's lemma: every irreducible actual
operator realization `S` of `GL_n` over a number field `F` has a central character, a
continuous character `χ` of the idele class group `C_F` with `S.HasCentralCharacter χ`,
and `χ` is the only such character. -/
def IrreducibleCentralCharacterStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (S : OperatorRealization F n),
    S.IsIrreducible → ∃! χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ, S.HasCentralCharacter χ

end Langlands.Automorphic.OperatorRealization
