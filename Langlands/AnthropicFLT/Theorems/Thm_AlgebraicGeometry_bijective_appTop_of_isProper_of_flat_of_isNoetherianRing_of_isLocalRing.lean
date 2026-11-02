/-
Ported from `Theorems/Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing
    {X : Scheme.{u}} {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A]
    (p : X ⟶ Spec A) [IsProper p] [Flat p]
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective p.appTop :=
  P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.solution p h
