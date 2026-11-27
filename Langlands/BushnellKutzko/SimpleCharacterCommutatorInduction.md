# Terminal and successor character commutator calculations

`simpleCharacterCommutatorAt_nil` proves both formulas at a terminal finite critical depth from the additive-character calculation. `simpleCharacterCommutatorAt_cons` uses the defining twist, evaluating the mixed and J commutators for the successor character. The scalar successor uses the determinant. The finite successor splits the positive mixed lattice into the relative and deeper summands and evaluates at the appropriate higher character depth. A J input below the cutoff is factored further into its relative and cutoff parts.

The perturbation coefficient lies in ambient filtration step `−r`. The bound `k + 2ℓ ≥ r + 1` in BK93 (3.2.6), printed p. 100, controls its commutator error and is used again in (3.2.8). The resulting value identity for the perturbation character is (3.2.9), printed p. 102.
