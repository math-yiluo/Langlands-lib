# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase`. Statement. `AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_locIsoOnBase`: if `M` and `M'` are locally
isomorphic over the base of `f : A ⟶ Spec S` (`LocIsoOnBase`), their geometric-fibre `H⁰` dimensions agree
at every `sk : S → k`.

Proof. The relation pulls back to the fibre over `Spec k` (ported
`Polarisation.LocIsoOnBase.pullback_of_comp_eq`), whose base is a point; there, local isomorphism over a
neighbourhood of the point is a global isomorphism, so the global sections have the same dimension (also
using `LocIsoOnBase.equivalence`, `LocIsoOnBase.tensor`, `Scheme.Modules.IsInvertible.pullback_dual_monoidalV2`
and `Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback` for the identification of fibres).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase.R2LocIso.locIsoOnBase_of_iso`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase.R2LocIso.dualIso`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase.R2LocIso.locIsoOnBase_dual`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase.R2LocIso.locIsoOnBase_mumfordBundle`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase.R2LocIso.geomFibreH0Finrank_eq_of_locIsoOnBase`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisationRosati` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback` (same contribution).
Other imports: `Mathlib`.
