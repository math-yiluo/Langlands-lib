# Base change of quasi-isomorphisms of bounded flat complexes: proof

`Langlands.Cohomology.ModuleComplex.boundedFlatQuasiIsoBaseChange.{u}` proves exactly the
published target `BoundedFlatQuasiIsoBaseChangeStatement.{u}`. It applies the ported theorem
`Module.quasiIso_baseChange_of_quasiIso_of_flat`; unfolding the proposition gives the same quantified type.

The implemented algebraic argument is described in the paired supporting
solution module
`Langlands/AnthropicFLT/P2M/Sol/S_Module_quasiIso_baseChange_of_quasiIso_of_flat.md`.
It uses the original natural-number indexing and explicit cycle and boundary
conditions throughout. It does not assert the geometric universal-perfect-
sections statement.

The support code is adapted from the registered Anthropic FLT source
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
`P2M/Sol/S_Module_quasiIso_baseChange_of_quasiIso_of_flat.lean` and its `Theorems/Thm_` wrapper.
Per-file headers and Markdown record the mechanical port changes and preserve
the Apache 2.0 notice. The wrapper in this file is an internal interface adapter
written by Worker 137. All universes and hypotheses are unchanged.
