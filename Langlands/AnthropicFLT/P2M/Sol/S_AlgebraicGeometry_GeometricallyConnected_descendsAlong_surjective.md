# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions) are replaced by `open` commands with the same namespaces (written `_root_.N` where the name would otherwise resolve inside the current namespace). Exception (manual edit): the first one (line 21) also listed `P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.AlgebraicGeometry`, which does not exist yet at that point (the next command creates it); `open` rejects it, so it is dropped, and the file compiles without it.
- 1 `p2m_export "N" "x y …"` command(s) (an FLT command from `P2M.Util` that adds, in the current namespace, aliases of the listed declarations of namespace `N`) are replaced by `export _root_.N (x y …)`, which adds the same aliases.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. Auxiliary lemma `geometricallyConnected_of_pullback_snd`: if `σ : S' ⟶ S` is surjective and the
base change `X ×_S S' ⟶ S'` of `f : X ⟶ S` is geometrically connected, then `f` is. Given a field
`K`, a point `k : Spec K ⟶ S` and a pullback square `Z = X ×_S Spec K`, pick a point `z` of
`Spec K ×_S S'` (`σ` is surjective) with residue field `L`; then `Spec L ⟶ Spec K` is surjective and
`Spec L` maps to `S'`. The pullback `Z ×_{Spec K} Spec L` is also the fibre of `X ×_S S' ⟶ S'` over
`Spec L ⟶ S'` (pasting of pullback squares), hence connected; it maps onto `Z`, so `Z` is connected.
`solution` turns this into `MorphismProperty.DescendsAlong` via `DescendsAlong.mk'`, using the
pullback symmetry and invariance of geometric connectedness under isomorphisms.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.AlgebraicGeometry.GeometricallyConnectedDescentAux.geometricallyConnected_of_pullback_snd`
- theorem `P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.solution`

The `export` adds, in namespace `P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.AlgebraicGeometry`, aliases of `AlgebraicGeometry.Surjective`, `Spec`, `Scheme`, `GeometricallyConnected` and `geometrically` (no new declarations).

## Dependencies

No ported FLT module is imported.
The module imports `Mathlib`.
