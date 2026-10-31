# Finiteness of the bottom row of a convergent spectral sequence (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_DoubleComplex_Convergence_finite_E2_q0`. Its declarations live in the
namespace `P2MW.S_DoubleComplex_Convergence_finite_E2_q0`.

## Statement

`solution`: let `R` be a noetherian ring and `conv : DoubleComplex.Convergence R E₂ H N` convergence data for
families of `R`-modules `E₂ p q` and `H n` (`Def_AlgebraicGeometry_DoubleComplex`). If every `H n` is finitely
generated and every `E₂ p q` with `q ≥ 1` is finitely generated, then `E₂ p 0` is finitely generated for every
`p ≤ N`. The theorem module `Theorems.Thm_DoubleComplex_Convergence_finite_E2_q0` states this as
`DoubleComplex.Convergence.finite_E2_q0` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…DoubleComplex`, section `Extract`.

1. `subquot_finite`: over a noetherian ring, a subquotient of a finitely generated module is finitely
   generated. `filt_finite`: if a finite increasing filtration starts at `⊥` and all its successive quotients
   are finitely generated, then every step is finitely generated.
2. `Convergence.finite_E2_q0`. The filtration `Bfilt p` of `E₂ p 0` has successive quotients isomorphic to
   subquotients of terms `E₂ p' q'` with `q' ≥ 1` (`Bfilt_gr`), so by `filt_finite` its top, the submodule `B`
   of `Einf p 0`, is finitely generated (`Bfilt_top`). The carrier `Z / B` of `Einf p 0` is isomorphic to the
   graded piece `Hfilt p (p + 1) / Hfilt p p` of `H p` (`Hfilt_gr`), a subquotient of the noetherian module
   `H p`, so it is finitely generated. Hence `Z` is finitely generated
   (`Module.Finite.of_submodule_quotient`), and `Z = ⊤` on the row `q = 0` (`hZ0`), so `E₂ p 0` is finitely
   generated.

## Provenance and licence

This file is a port of `P2M/Sol/S_DoubleComplex_Convergence_finite_E2_q0.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_DoubleComplex` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_DoubleComplex`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed. Each
  `p2m_open_scoped "N" in` becomes `open scoped _root_.N in`. These replacements change no declaration,
  statement or proof step.
