# Proof of flatness transport across a surjective map with bijective base change

`Langlands.Algebra.surjectiveBaseChangeFlatnessTransport` proves exactly
`Langlands.Algebra.SurjectiveBaseChangeFlatnessTransportStatement`, with all five
independent universe parameters and no additional hypotheses.

The private helper `transport` treats four rings A, S, C and D. It assumes that
A to S is surjective, C to D is bijective, and the two algebra structures on D
are compatible with A. The module M has compatible A and S actions.

First, `LinearEquiv.ofBijective` turns the actual algebra map C to D into a
C-linear equivalence. Its inverse and `Module.Flat.of_linearEquiv` show that
D is flat over C. `Module.Flat.trans` then restricts the assumed flatness of
D tensor_S M to C.

Next, `TensorProduct.CompatibleSMul.of_algebraMap_surjective` uses the actual
surjective map A to S to show that balancing over A already balances the
S-actions. `TensorProduct.equivOfCompatibleSMul` identifies
D tensor_A M with D tensor_S M as C-modules. Meanwhile
`TensorProduct.AlgebraTensorModule.congr` tensors the C-linear equivalence
C to D with the identity of M over A. Composing these two equivalences and
applying `Module.Flat.of_linearEquiv` proves the helper.

The main theorem takes C = A tensor_R T and D = S tensor_R T. It installs the
C-algebra structure on D from the specified tensor map, and checks the
A to C to D scalar tower on elements of A using the pure-tensor formula.
All other scalar structures are the canonical ones already in the statement.
The helper now gives the asserted flatness of C tensor_A M.

This proof uses Mathlib's flatness and tensor APIs. It does not rely on the
local flatness criterion or on a proof of 05UV. The paired statement Markdown
explains the derived provenance and the specialization to quotient residue
fibres in the source proof of Stacks tag 05UV.
