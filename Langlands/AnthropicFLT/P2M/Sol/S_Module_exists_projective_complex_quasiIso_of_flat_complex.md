# Finite projective replacements for bounded flat complexes

This module ports `P2M/Sol/S_Module_exists_projective_complex_quasiIso_of_flat_complex.lean` from Anthropic FLT. All carrier types
are in the arbitrary universe `u`, exactly as in the original theorem.

## Implemented proof

The construction descends through finite free models in positive degrees, represented by finitely supported sequences with a chosen finite bound. At each step it adds generators both for the required relations and for finite cohomology. After the descending construction, an exact tail and flat-kernel induction establish flatness of the final degree-zero kernel; finite cohomology and noetherianity make it finite, hence projective. The resulting complex is finite projective in every degree and has the specified upper bound. Explicit cycle and boundary arguments prove that its chain map to the original complex is a quasi-isomorphism.

## Provenance and port changes

Registered source: `anthropic-flt-complete-lean-source-6e837e75`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, file
`P2M/Sol/S_Module_exists_projective_complex_quasiIso_of_flat_complex.lean` (complete file).

Only the FLT import prefix, removal of `P2M.Util`, replacement of its wrapper
commands by ordinary Lean commands, finite heartbeat limits and the port
transparency option have changed. Declaration names, types and mathematical
proof steps are preserved. This supporting module is part of the focused
bounded-flat algebra proof unit; it asserts no geometric comparison.

Copyright 2026 Anthropic. Apache License 2.0; see
`licenses/Anthropic-FLT/LICENSE` and `licenses/Anthropic-FLT/NOTICE`.
