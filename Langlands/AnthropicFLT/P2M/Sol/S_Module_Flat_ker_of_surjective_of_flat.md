# Kernels of surjections between flat modules

This module ports `P2M/Sol/S_Module_Flat_ker_of_surjective_of_flat.lean` from Anthropic FLT. All carrier types
are in the arbitrary universe `u`, exactly as in the original theorem.

## Implemented proof

The kernel of a surjection M → P between flat R-modules is flat. The proof tests tensor preservation of injections. The preceding pure-injection lemma embeds each tensor product with the kernel into the corresponding tensor product with M; flatness of M and commutation of the tensor square then imply injectivity for the kernel.

## Provenance and port changes

Registered source: `anthropic-flt-complete-lean-source-6e837e75`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, file
`P2M/Sol/S_Module_Flat_ker_of_surjective_of_flat.lean` (complete file).

Only the FLT import prefix, removal of `P2M.Util`, replacement of its wrapper
commands by ordinary Lean commands, finite heartbeat limits and the port
transparency option have changed. Declaration names, types and mathematical
proof steps are preserved. This supporting module is part of the focused
bounded-flat algebra proof unit; it asserts no geometric comparison.

Copyright 2026 Anthropic. Apache License 2.0; see
`licenses/Anthropic-FLT/LICENSE` and `licenses/Anthropic-FLT/NOTICE`.
