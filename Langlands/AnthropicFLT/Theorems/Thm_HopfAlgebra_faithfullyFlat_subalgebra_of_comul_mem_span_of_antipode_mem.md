# Faithful flatness over every stable Hopf subalgebra — theorem interface

For any field k and finite type commutative Hopf algebra H, every k-subalgebra K stable under comultiplication in the stated tensor-span sense and under the antipode makes H a faithfully flat K-module. K need not be finitely generated. The universes of k and H are independent. There is no perfectness, reducedness, smoothness or cocommutativity assumption.

The theorem `HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem` applies the companion `P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem.md):

First work over an algebraically closed field. For a finitely generated stable K₀, positive characteristic is handled by the perfect-field reduction to reduced subalgebras. In characteristic zero, Cartier's theorem makes H reduced, so K₀ is reduced as a subalgebra and the reduced case applies. Every finite subset of a general K lies in a finitely generated stable subalgebra. These subalgebras form a nonempty directed cover, and the directed-union theorem gives faithful flatness over K.

For a general field, extend to its algebraic closure. Tensor induction and the formulas for base-changed comultiplication and antipode prove stability of the range of k' tensor K in k' tensor H. Apply the algebraically closed case there, then the field-extension descent theorem. The characteristic and reducedness restrictions occur only in intermediate lemmas and have been discharged before the conclusion.

Source: `Theorems/Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `12e2307a1f2c8d716d82af94e267ae11b12fda378ebadff71e8f07e84d9e6124`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
