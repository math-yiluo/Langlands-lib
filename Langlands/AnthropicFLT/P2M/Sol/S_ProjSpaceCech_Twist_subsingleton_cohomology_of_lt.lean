/-
Ported from `P2M/Sol/S_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped and its commands are replaced
by standard Lean commands. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function

namespace ProjSpaceCech
export _root_.ProjSpaceCech (Twist.cochain_subsingleton_of_lt Twist.H)
open _root_.ProjSpaceCech

section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

namespace Twist export _root_.ProjSpaceCech.Twist (d cochain_subsingleton_of_lt H) end Twist
open scoped _root_.ProjSpaceCech.Twist in

theorem Twist.subsingleton_cohomology_of_lt {i : ℕ} (hi : n < i) :
    Subsingleton (Twist.H R n d i) := by
  rcases i with _ | j
  · exact absurd hi (Nat.not_lt_zero n)
  dsimp only [Twist.H]
  have hsub := Twist.cochain_subsingleton_of_lt R n d hi
  exact ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    congrArg _ (Subtype.ext (hsub.elim a.1 b.1))⟩

end Cohomology

end ProjSpaceCech

theorem solution (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {i : ℕ}
    (hi : n < i) : Subsingleton (ProjSpaceCech.Twist.H R n d i) :=
  ProjSpaceCech.Twist.subsingleton_cohomology_of_lt R n d hi

end
