# Base change of quasi-isomorphisms of bounded flat complexes

This module ports `P2M/Sol/S_Module_quasiIso_baseChange_of_quasiIso_of_flat.lean` from Anthropic FLT. All carrier types
are in the arbitrary universe `u`, exactly as in the original theorem.

## Implemented proof

The proof builds a shifted cone with degree zero K 0 and degree i+1 equal to K(i+1) × C i. Its differential sends a pair to (δ x, φ x − d y). The four cycle and boundary conditions for φ are equivalent to exactness of this cone. The cone is bounded and termwise flat. The preceding bounded-exact-flat lemma gives its exactness after arbitrary scalar extension. The tensor/product equivalence identifies this tensor cone with the cone of the base-changed map, and the converse cycle argument gives the conclusion.

## Provenance and port changes

Registered source: `anthropic-flt-complete-lean-source-6e837e75`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, file
`P2M/Sol/S_Module_quasiIso_baseChange_of_quasiIso_of_flat.lean` (complete file).

Only the FLT import prefix, removal of `P2M.Util`, replacement of its wrapper
commands by ordinary Lean commands, finite heartbeat limits and the port
transparency option have changed. Declaration names, types and mathematical
proof steps are preserved. This supporting module is part of the focused
bounded-flat algebra proof unit; it asserts no geometric comparison.

Copyright 2026 Anthropic. Apache License 2.0; see
`licenses/Anthropic-FLT/LICENSE` and `licenses/Anthropic-FLT/NOTICE`.
