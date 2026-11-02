# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral`. Statement. `AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral`: for an integral scheme `X` proper over
an algebraically closed field `k`, the map `k → Γ(X, ⊤)` is bijective.

Proof. `Γ(X, ⊤)` is a domain (integrality) and the map is injective. A global section `a` defines a morphism
`X ⟶ 𝔸¹_k` through `X ⟶ Spec Γ(X, ⊤)`; its image is proper over `k`. If it were surjective onto `𝔸¹_k`,
then `𝔸¹_k ⟶ Spec k` would be proper and integral, so `k[X]` would be finite over `k`, which is false
(`Polynomial.not_finite`). So the image is a proper closed subset, i.e. finitely many closed points; as `X` is
irreducible it is a single `k`-point `c`, and `a - c` is nilpotent, hence zero: `a = c`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
