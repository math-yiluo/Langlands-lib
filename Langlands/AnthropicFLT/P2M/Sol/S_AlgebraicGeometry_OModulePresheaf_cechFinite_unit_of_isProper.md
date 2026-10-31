# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions) are replaced by `open` commands with the same namespaces (written `_root_.N` where the name would otherwise resolve inside the current namespace). Exception (manual edit): the first one (line 26) also listed `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper.AlgebraicGeometry`, which does not exist yet at that point (the next command creates it); `open` rejects it, so it is dropped, and the file compiles without it.
- 2 `p2m_export "N" "x y …"` command(s) (an FLT command from `P2M.Util` that adds, in the current namespace, aliases of the listed declarations of namespace `N`) are replaced by `export _root_.N (x y …)`, which adds the same aliases.
- No other change: the declarations, statements and proofs are the FLT text. The FLT `attribute [-…]`
  lines after the namespace header (which locally deactivate instances and simp lemmas declared in
  imported FLT modules) are kept unchanged.

## Content

Proof: apply the C1 theorem `AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper` (finiteness
of Čech cohomology of coherent quasi-coherent module presheaves on a proper scheme over a noetherian
ring) to the structure presheaf `OModulePresheaf.unit π`. The two hypotheses are checked here:
`isCoherent_unit` (each `Γ(V, U)` is a finite module over itself) and `isQuasicoherent_unit` (on an
affine open `U`, sections over the basic open `D(f)` are the localization of `Γ(V, U)` at the powers of
`f`, `IsAffineOpen.isLocalization_basicOpen`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper.AlgebraicGeometry.OModulePresheaf.isCoherent_unit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper.AlgebraicGeometry.OModulePresheaf.isQuasicoherent_unit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper.solution`

The two `export` commands add aliases (no new declarations) in the local namespaces
`P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper.AlgebraicGeometry` and
`….AlgebraicGeometry.OModulePresheaf` of the listed `AlgebraicGeometry` and
`AlgebraicGeometry.OModulePresheaf` declarations.

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library, ported by task `69435287-9f1e-4abd-8483-5e65ff23668a`), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` (Library, ported by task `69435287-9f1e-4abd-8483-5e65ff23668a`).
Mathlib imports: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.RingTheory.Noetherian.Basic` (as in FLT; this module does not import all of `Mathlib`).
