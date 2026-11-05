# Translations on a commutative Hopf algebra — theorem interface

Given algebra maps τ(g) defined by applying g to the first factor of comultiplication, every τ(g) is bijective. Translation preserves every subalgebra stable under comultiplication in the stated span sense. For any two k-points x,y of H, there is g with y = x composed with τ(g). No cocommutativity is assumed.

The theorem `HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq` applies the companion `P2MW.S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.md):

The solution defines the corresponding linear translation T and compares it with τ. Coassociativity gives its composition law in terms of convolution. Composing a point with the antipode provides its convolution inverse, so T(g) has a two-sided inverse. The same convolution calculation constructs g taking x to y. Span induction proves preservation of a stable subalgebra: contraction of a tensor with both factors in K is a scalar multiple of its second factor, which remains in K.

Source: `Theorems/Thm_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `403389fd523b46484f0d788170088fd16233866c49b03ce517551313ca01055f`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
