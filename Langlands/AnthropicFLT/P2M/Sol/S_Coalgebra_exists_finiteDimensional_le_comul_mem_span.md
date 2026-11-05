# A finite dimensional subcoalgebra through an element

If K is a subspace of a coalgebra C over a field k and comultiplication takes K into the span of tensors with both factors in K, then each x in K belongs to a finite dimensional subspace D contained in K with the same comultiplication property. The statement imposes no finiteness condition on C or K.

Starting from a finite tensor expansion of Δ(x), choose independent right coefficients and extend their coordinate functionals to C. Contraction produces a finite dimensional right coideal N contained in K and containing x. Choose independent generators of N and contract on the left. The resulting matrix coefficients v(j,m) belong to K and satisfy Δ(v(l,m)) = sum_j v(l,j) tensor v(j,m), by coassociativity. Their finite span is D. The counit identities put N, hence x, in D. The contraction and dual-family lemmas implement these two finite coefficient arguments.

Source: `P2M/Sol/S_Coalgebra_exists_finiteDimensional_le_comul_mem_span.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `6d09ec2221cbca68a1c2d597272b36918d40634039fce2ddd92f09614a358ed9`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. Tensor inductions explicitly select the three-case recursor where the current default eliminator has changed.
