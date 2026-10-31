# `Langlands.AnthropicFLT.P2M.Sol.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof of the Krull–Akizuki theorem (namespace `KrullAkizukiLa`), via lengths of quotients
`M ⧸ aM` (`smulRange a M` is the submodule `aM`).

- Domain facts: for `A` a noetherian domain of dimension `≤ 1` and `d ≠ 0`, `A ⧸ (d)` is artinian,
  so a finite `A`-module killed by `d ≠ 0` has finite length.
- Filtrations: if `a` acts injectively on `M`, then `length(M ⧸ a^k M) = k · length(M ⧸ aM)`
  (`length_quot_pow`), plus comparison lemmas for submodules and isomorphic modules.
- Core: let `P` be a torsion-free `A`-module containing a finitely generated submodule `E` with
  `P ⧸ E` torsion. For `a ≠ 0`, every finitely generated `M₁ ⊇ E` has
  `length(M₁ ⧸ aM₁) ≤ length(E ⧸ aE)` (`length_quot_le_of_fg`: `d M₁ ⊆ E` for some `d ≠ 0`, compare
  the filtrations by powers of `a`), so every finitely generated submodule of `P ⧸ aP` has length at
  most `length(E ⧸ aE) < ∞` (`length_le_of_fg_quot`), hence `P ⧸ aP` has finite length (`core`).
- Lattice: for an injective `A`-linear map from `P` into a finite-dimensional `K`-vector space,
  such an `E` exists (`exists_lattice`, clearing denominators of a basis).
- Main (`main`): apply this to `P = B ⊆ L`. Every nonzero ideal `J` of `B` contains a nonzero
  `a ∈ A` (`B` is algebraic over `A`), so `B ⧸ J` is a quotient of `B ⧸ aB` and has finite length.
  Hence every nonzero ideal is finitely generated modulo `aB` (noetherian `B ⧸ aB`), so `B` is
  noetherian; and for a nonzero prime `p`, `B ⧸ aB` is artinian, so `p` is maximal
  (`Ring.DimensionLEOne B`). `solution` applies `main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.smulRange`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.mem_smulRange_iff`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.smul_mem_smulRange`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.le_of_forall_mul_le`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.isArtinianRing_quotient_span_singleton`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.length_ne_top_of_isTorsionBy`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.pow_smul_injective`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.smulRange_pow_succ_le`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.length_quot_pow`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.length_quot_le`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.length_quot_smulRange_eq_of_equiv`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.length_quot_le_of_fg`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.length_le_of_fg_quot`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.length_ne_top_of_forall_fg_le`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.core`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.exists_smul_mem_span`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.exists_lattice`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.main`
- theorem `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.solution`

## Dependencies

No ported FLT module is imported.
The module imports `Mathlib`.
