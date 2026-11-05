# Finite Hopf subalgebras containing a finite subset — theorem interface

For a commutative Hopf algebra H over a field k and a subalgebra K stable under comultiplication in the stated tensor-span sense and under the antipode, every finite subset of K is contained in a finitely generated subalgebra K₀ of K with both stability properties.

The theorem `HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset` applies the companion `P2MW.S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset.md):

Apply the finite dimensional subcoalgebra theorem to each of the finitely many elements and take their finite sum D. Enlarge D to D + S(D). The anti-coalgebra identity for S preserves comultiplication stability; S squared equal to the identity makes the enlargement stable under S. Adjoin this finite dimensional subspace as an algebra. Finite generation follows from a finite vector-space spanning set, and algebra-adjoin induction extends the two stability properties to K₀.

Source: `Theorems/Thm_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `b49b18f025d16cfa0d6d05ab163b140eec0e7553bbfdfa79dc48009a2f92fd12`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
