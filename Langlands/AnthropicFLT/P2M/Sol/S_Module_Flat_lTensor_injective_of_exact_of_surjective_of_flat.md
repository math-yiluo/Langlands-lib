# Pure tensor injections with flat quotient

This module ports `P2M/Sol/S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.lean` from Anthropic FLT. All carrier types
are in the arbitrary universe `u`, exactly as in the original theorem.

## Implemented proof

For a short exact sequence N → M → P with flat quotient P, tensoring the injection with any R-module A is injective. The implemented proof first chooses a free presentation K → F → A. A tensor-square identity lets a diagram chase use exactness of the rows, flatness of F and P, and surjectivity from F tensor N to A tensor N. The solution instantiates this chase with the standard free presentation on the underlying elements of A.

## Provenance and port changes

Registered source: `anthropic-flt-complete-lean-source-6e837e75`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, file
`P2M/Sol/S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.lean` (complete file).

Only the FLT import prefix, removal of `P2M.Util`, replacement of its wrapper
commands by ordinary Lean commands, finite heartbeat limits and the port
transparency option have changed. Declaration names, types and mathematical
proof steps are preserved. This supporting module is part of the focused
bounded-flat algebra proof unit; it asserts no geometric comparison.

Copyright 2026 Anthropic. Apache License 2.0; see
`licenses/Anthropic-FLT/LICENSE` and `licenses/Anthropic-FLT/NOTICE`.
