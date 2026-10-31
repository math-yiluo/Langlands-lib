/-
Ported from `Theorems/Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
    {k : Type u} [CommRing k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type u) [CommRing A] [Algebra k A] [Module.Flat k A] :
    IsPushout (CommRingCat.ofHom (algebraMap k A))
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop)
      (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop :=
  P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.solution fX A
