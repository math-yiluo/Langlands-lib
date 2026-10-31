# Finite projective replacements for bounded flat complexes: proof

`Langlands.Cohomology.ModuleComplex.boundedFlatComplexProjective.{u}` proves exactly the
published target `BoundedFlatComplexProjectiveStatement.{u}`. It applies the ported theorem
`Module.exists_projective_complex_quasiIso_of_flat_complex`; unfolding the proposition gives the same quantified type.

The implemented algebraic argument is described in the paired supporting
solution module
`Langlands/AnthropicFLT/P2M/Sol/S_Module_exists_projective_complex_quasiIso_of_flat_complex.md`.
It uses the original natural-number indexing and explicit cycle and boundary
conditions throughout. It does not assert the geometric universal-perfect-
sections statement.

The support code is adapted from the registered Anthropic FLT source
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
`P2M/Sol/S_Module_exists_projective_complex_quasiIso_of_flat_complex.lean` and its `Theorems/Thm_` wrapper.
Per-file headers and Markdown record the mechanical port changes and preserve
the Apache 2.0 notice. The wrapper in this file is an internal interface adapter
written by Worker 137. All universes and hypotheses are unchanged.
