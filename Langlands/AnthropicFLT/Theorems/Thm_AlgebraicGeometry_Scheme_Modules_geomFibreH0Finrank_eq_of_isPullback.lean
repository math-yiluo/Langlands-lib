/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X A' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of S'))
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom φ)))
    (M : X.Modules) (M' : A'.Modules) (e : (Scheme.Modules.pullback c).obj M ≅ M')
    (K : Type u) [Field K] (sK : S' →+* K) :
    Scheme.Modules.geomFibreH0Finrank f' M' K sK = Scheme.Modules.geomFibreH0Finrank f M K (sK.comp φ) :=
  P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.solution φ f f' c hc M M' e K sK
