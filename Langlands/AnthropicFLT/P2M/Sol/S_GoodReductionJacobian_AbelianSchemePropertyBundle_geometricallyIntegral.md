# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral`

Ported for the proof of projective representability of the relative endomorphism functor of a projective abelian scheme. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: apart from the renames described under “Names changed by the Library” below, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral`. Statement. `GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral`: over a field `k`, a scheme with the
abelian-scheme property bundle is geometrically integral.

Proof. Over a field, `A` is smooth, so its stalks are regular local rings and hence domains (ported
`Smooth.isRegularLocalRing_stalkFLT`, `IsRegularLocalRing.isDomainFLT`); being connected and locally noetherian it is
integral (ported `isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk`; local
`isIntegral_of_smooth_of_connectedSpace`). Section `Stacks04KV`: a connected scheme with a rational point (the
unit section) is geometrically connected (ported `GeometricallyConnected.descendsAlong_surjective`,
`GeometricallyIrreducible.geometricallyConnectedFLT`, local `connectedSpace_pullback`). Every base change to a field
is then smooth and connected, hence integral by the same argument; with the ported
`geometricallyIntegral_of_isAlgClosed` this gives geometric integrality.

## Declarations

Names, namespaces and statements are the FLT ones, apart from the renames described under “Names changed by the Library” below. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.isIntegral_of_smooth_of_connectedSpace`
- scoped instance `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field`
- scoped instance `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.nonempty_spec_field`
- abbrev `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.bc`
- def `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.pt'`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.pt'_fst`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_pullback_section`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.eq_pt'_of_fst_eq`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.connectedSpace_pullback`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (ported with this file), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk` (ported with this file), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk` (ported with this file), `Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain` (ported with this file), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed` (ported with this file), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected` (ported with this file), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective` (Library).
Other imports: `Langlands.MathlibBase`.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- its uses of `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected`, `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`, `IsRegularLocalRing.isDomain` are uses of `geometricallyConnectedFLT`, `isRegularLocalRing_stalkFLT`, `isDomainFLT` now.

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are.
