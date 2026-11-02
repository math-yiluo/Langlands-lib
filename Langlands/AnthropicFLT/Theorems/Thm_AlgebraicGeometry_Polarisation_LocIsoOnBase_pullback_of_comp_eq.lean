/-
Ported from `Theorems/Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
    {S S' : Type u} [CommRing S] [CommRing S'] {X Y : Scheme.{u}}
    {g : X ⟶ Spec (CommRingCat.of S)} (g' : Y ⟶ Spec (CommRingCat.of S')) (h : Y ⟶ X)
    (φ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (comm : h ≫ g = g' ≫ φ)
    {M M' : X.Modules} (hM : LocIsoOnBase g M M') :
    LocIsoOnBase g' ((Scheme.Modules.pullback h).obj M) ((Scheme.Modules.pullback h).obj M') :=
  P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq.solution g' h φ comm hM
