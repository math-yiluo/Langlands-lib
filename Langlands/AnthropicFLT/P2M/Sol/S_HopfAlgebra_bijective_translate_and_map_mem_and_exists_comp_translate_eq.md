# Translations on a commutative Hopf algebra

Given algebra maps τ(g) defined by applying g to the first factor of comultiplication, every τ(g) is bijective. Translation preserves every subalgebra stable under comultiplication in the stated span sense. For any two k-points x,y of H, there is g with y = x composed with τ(g). No cocommutativity is assumed.

The solution defines the corresponding linear translation T and compares it with τ. Coassociativity gives its composition law in terms of convolution. Composing a point with the antipode provides its convolution inverse, so T(g) has a two-sided inverse. The same convolution calculation constructs g taking x to y. Span induction proves preservation of a stable subalgebra: contraction of a tensor with both factors in K is a scalar multiple of its second factor, which remains in K.

Source: `P2M/Sol/S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `8074ef570248f937ef2fe480368e74fe36efd11af6974f137a3fccd9da7ec67e`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. Tensor inductions explicitly select the three-case recursor where the current default eliminator has changed.
