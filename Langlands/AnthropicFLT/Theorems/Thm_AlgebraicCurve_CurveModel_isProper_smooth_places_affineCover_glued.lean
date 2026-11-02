/-
Ported from `Theorems/Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IntermediateField

universe u

namespace AlgebraicCurve.CurveModel

theorem isProper_smooth_places_affineCover_glued (K : Type u) [Field K] [Infinite K]
    [PerfectField K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    (ht : Transcendental K t) [FiniteDimensional ↥K⟮t⟯ L] [Algebra.IsSeparable ↥K⟮t⟯ L] :
    IsProper (gluedToBase K t) ∧
    SmoothOfRelativeDimension 1 (gluedToBase K t) ∧
    (∃ P : closedPoints (glued K t) → Place K L, Function.Bijective P ∧
      ∀ x : closedPoints (glued K t),
        (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
            (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
          (P x).toValuationSubring.toSubring) ∧
    (∀ F : Finset (glued K t), ∃ U : (glued K t).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :=
  P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.solution K t ht
