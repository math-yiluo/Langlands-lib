# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry _root_.TopologicalSpace _root_.Polynomial _root_.AlgebraicGeometry.Polynomial`: namespace `P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry` dropped.
- 4 `p2m_open_scoped "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that activates the scoped extensions of the named namespaces without opening them) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces; a trailing ` in` is kept.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper`. Statement. `AlgebraicGeometry.exists_eq_snd_comp_of_comp_eq_const_of_isProper` (rigidity lemma): let `X` be proper and
integral over a field `k` with a rational point `x₀`, `Y` connected with a rational point `y₀`, `Z` separated
over `k`, and `φ : X ×_k Y ⟶ Z` over `k` such that `φ(-, y₀)` is constant with value `z₀`. Then `φ` factors
through the projection to `Y`: `φ = pr₂ ≫ φ(x₀, -)`.

Proof (Mumford's rigidity argument). For proper integral `X` with a rational point, `k → Γ(X, ⊤)` is bijective
(`bijective_algebraMap_appTop_of_isProper_of_isIntegral_of_section`, proved in this file), and the same holds after
any base change (ported `bijective_appTop_pullback_snd_of_bijective_appTop`; local
`RigidityAux.bijective_app_pullback_snd_of_isAffineOpen`).
Take an affine open `V ∋ z₀` of `Z`; the set of `y` with `φ(X × {y}) ⊆ V` is open (properness, the projection is
closed) and closed (connectedness argument), hence all of `Y` (local
`exists_opens_ι_comp_eq_of_isClosedMap_of_app_bijective_of_isAffineOpen`).
Over it, `φ` corresponds to a ring map `Γ(V) → Γ(X ×_k Y)` which factors through `Γ(Y)` since global functions
of `X ×_k Y'` come from `Y'`; this gives the factorization.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry.AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral_of_section`
- theorem `P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry.AlgebraicGeometry.exists_opens_ι_comp_eq_of_isClosedMap_of_app_bijective_of_isAffineOpen`
- theorem `P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.RigidityAux.bijective_iso_comp_iso_iff`
- theorem `P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry.AlgebraicGeometry.AlgebraicGeometry.RigidityAux.bijective_app_pullback_snd_of_isAffineOpen`
- theorem `P2MW.S_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper.AlgebraicGeometry.AlgebraicGeometry.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop` (same contribution).
Other imports: `Mathlib`.
