/-
Ported from `P2M/Sol/S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra

set_option autoImplicit false

universe u v w

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (B : Subalgebra R L) :
    IsNoetherianRing ↥B ∧ ringKrullDim ↥B ≤ 1 := by
  haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hR
  obtain ⟨hN, hD, -⟩ :=
    Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite (K := K) B
  haveI := hD
  exact ⟨hN, Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ↥B)⟩
