# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry _root_.TopologicalSpace _root_.Opposite`: namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry` dropped.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral`. Statement. `AlgebraicGeometry.OModulePresheaf.forall_pushforward_of_isIntegral`: let `π : V ⟶ Spec R` be proper
over a noetherian ring, `Z₀` a nonempty closed set with integral reduced subscheme `i : Z ⟶ V`, and `Q`
a predicate on FLT presheaves that holds for zero presheaves, satisfies two-out-of-three on short
exact sequences of coherent quasi-coherent presheaves, holds for `i_* 𝒪_Z`, and holds for all coherent
quasi-coherent presheaves supported in proper closed subsets of `Z₀`. Then `Q` holds for `i_* H` for
every presheaf `H` on `Z` whose pushforward is coherent, quasi-coherent and supported in `Z₀`.

Proof (namespace `AlgebraicGeometry.OModulePresheaf.PivotQAux`). Auxiliary results: the vanishing ideal
of `Z` has support `Z`; `V` is noetherian; kernels, images and cokernels of coherent (quasi-coherent)
presheaves are coherent (quasi-coherent), as are finite products, powers, restrictions to opens with
affine intersections, and `i_* 𝒪_Z`; `affSESPowSucc` (`0 → Fᵐ → Fᵐ⁺¹ → F → 0`) and `pow_of_ext` (`Q` holds
for powers). Main argument: by generic freeness (ported
`OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral`) there are a basic open `W₀ = D(f)`
meeting `Z₀` and sections `y₁, …, y_r` making `i_* H` free of rank `r` on affine opens inside `W₀`. Let
`Z₁ = Z₀ \ W₀ ⊊ Z₀`. The presheaf `P = ker (G × 𝒪^r → G|_{W₀})` (`δ`) comes with maps `α : P → G`,
`β : P → 𝒪^r` that are bijective on affine opens disjoint from `Z₁`; their kernels and cokernels are
coherent, quasi-coherent and supported in `Z₁`, so `Q` holds for them by hypothesis, and the
two-out-of-three property transfers `Q` from `𝒪^r` (`pow_of_ext`) to `P` and then to `G = i_* H`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.support_vanishingIdeal'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isNoetherian_of_isProper`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isCoherent_ker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isCoherent_im`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isCoherent_coker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isQuasicoherent_coker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isQuasicoherent_ker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isQuasicoherent_im`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isCoherent_prod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isQuasicoherent_prod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isCoherent_pow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isQuasicoherent_pow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isQuasicoherent_restrOpen`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isCoherent_pushforwardUnit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isQuasicoherent_unit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.isQuasicoherent_pushforwardUnit`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.affSESPowSucc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf.PivotQAux.pow_of_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral` (Library).
Other imports: `Mathlib`.
