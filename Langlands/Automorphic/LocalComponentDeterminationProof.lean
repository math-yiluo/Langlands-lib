import Langlands.Automorphic.LocalComponentDeterminationForward
import Langlands.Automorphic.LocalComponentDeterminationReverse
import Langlands.Automorphic.LocalComponentExistenceProof

/-!
# Automorphic representations are determined by their local components

Proof of `LocalComponentDeterminationStatement` (Getz–Hahn, Theorem 6.3.7 and the uniqueness of
the factors; Flath, Theorem 3): two irreducible jointly admissible operator subquotients of
`GL_(r+1)` are equivalent exactly when at every place some irreducible local representation is
a local component of both.

* "⇒" is `localComponentDetermination_forward` (`LocalComponentDeterminationForward`).
* "⇐" is `localComponentDetermination_reverse` (`LocalComponentDeterminationReverse`).

Both use the local components supplied by `localComponentExistence`
(`LocalComponentExistenceProof`).
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Automorphic

/-- **Automorphic representations are determined by their local components** (Getz–Hahn,
Theorem 6.3.7; Flath, Theorem 3). -/
theorem localComponentDetermination : LocalComponentDeterminationStatement.{u} := by
  intro F _ _ r Q Q' hQ _
  exact ⟨localComponentDetermination_forward localComponentExistence F r Q Q' hQ,
    localComponentDetermination_reverse localComponentExistence F r Q Q' hQ⟩

end Langlands.Automorphic
