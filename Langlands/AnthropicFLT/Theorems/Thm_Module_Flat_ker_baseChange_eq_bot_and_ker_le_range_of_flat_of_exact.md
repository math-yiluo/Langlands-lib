# Base change of bounded exact flat complexes

This module ports `Theorems/Thm_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact.lean` from Anthropic FLT. All carrier types
are in the arbitrary universe `u`, exactly as in the original theorem.

## Implemented proof

This theorem exposes the corresponding `P2MW.S_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact.solution` under the original public declaration name. The proof applies that solution to the original explicit parameters in order. The paired solution module explains the implemented proof.

## Provenance and port changes

Registered source: `anthropic-flt-complete-lean-source-6e837e75`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, file
`Theorems/Thm_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact.lean` (complete file).

Only the FLT import prefix, removal of `P2M.Util`, replacement of its wrapper
commands by ordinary Lean commands, finite heartbeat limits and the port
transparency option have changed. Declaration names, types and mathematical
proof steps are preserved. This supporting module is part of the focused
bounded-flat algebra proof unit; it asserts no geometric comparison.

Copyright 2026 Anthropic. Apache License 2.0; see
`licenses/Anthropic-FLT/LICENSE` and `licenses/Anthropic-FLT/NOTICE`.
