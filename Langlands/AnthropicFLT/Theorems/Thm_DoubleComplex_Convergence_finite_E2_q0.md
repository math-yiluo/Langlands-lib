# Finiteness of the bottom row of a convergent spectral sequence

Module `Langlands.AnthropicFLT.Theorems.Thm_DoubleComplex_Convergence_finite_E2_q0`.

## Statement

`DoubleComplex.Convergence.finite_E2_q0`: for a noetherian ring `R`, families of `R`-modules `E₂ p q` and
`H n`, `conv : DoubleComplex.Convergence R E₂ H N`, `hH : ∀ n, Module.Finite R (H n)`,
`hE₂ : ∀ p q, 1 ≤ q → Module.Finite R (E₂ p q)` and `p ≤ N`, `Module.Finite R (E₂ p 0)`.

## Proof

`exact @_root_.P2MW.S_DoubleComplex_Convergence_finite_E2_q0.solution R _ _ E₂ _ _ H _ _ N conv hH hE₂ p hp`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes the
proof.

## Provenance and licence

This file is a port of `Theorems/Thm_DoubleComplex_Convergence_finite_E2_q0.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The
theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_DoubleComplex` and the corresponding
  `P2M.Sol` module are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied to
  the theorem's arguments in order (`_` for instance arguments).
