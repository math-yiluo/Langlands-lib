/-
Ported from `Theorems/Thm_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
    {A : Type u} [CommRing A] [IsJacobsonRing A]
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hne : U.Nonempty)
    (htrans : ∀ P Q : PrimeSpectrum A, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal → P ∈ U → Q ∈ U) :
    U = Set.univ := by
  exact _root_.P2MW.S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.solution U hU hne htrans
