/-
Ported from `Theorems/Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface
import Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u
theorem GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    AbelianSchemePropertyBundle (RelativeGroupLaw.baseResidueField s) (RelativeGroupLaw.fibreStr f s) :=
  P2MW.S_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr.solution hA s
