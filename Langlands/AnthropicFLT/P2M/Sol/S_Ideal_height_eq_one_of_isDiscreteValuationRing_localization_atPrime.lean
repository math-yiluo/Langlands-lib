/-
Ported from `P2M/Sol/S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (h : IsDiscreteValuationRing (Localization.AtPrime p)) : p.height = 1 := by
  haveI := h
  have hnf : ¬ IsField (Localization.AtPrime p) := fun hF =>
    IsDiscreteValuationRing.not_a_field (R := Localization.AtPrime p)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)
  have hd1 : ringKrullDim (Localization.AtPrime p) = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one (Localization.AtPrime p) hnf
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)] at hd1
  exact_mod_cast hd1
