# Duality and twisting of actual exact expansions

This internal helper proves transport of the published exact-expansion relation under genuine duality and continuous character twists. Its immediate consumer is the local-element construction for `Langlands.Global.PoleComparison.RelativeIsometryOperationStatement.{uF, uW, uP}`. It proves no global generator-existence or local Langlands statement.

The generic group and representation-carrier universes remain independent. Character twisting requires a continuous complex character; duality additionally requires a topological group. No semisimplicity or existence of irreducible expansions is asserted.

`basisContinuousClass_twistBasisEquiv` and `basisContinuousClass_dualBasisEquiv` compare the same actual transformed representatives on the two isomorphism-class quotients. Quotient induction proves these identities. The theorems `realizeExact_twistLatticeEquiv` and `realizeExact_dualLatticeEquiv` then use integral linear induction, with the generator identities of `realizeExact`, to show that the canonical realization into exact K0 intertwines the corresponding operations.

`Weil.ExactExpansion.twist` and `.dual` apply these identities to any supplied exact expansion. The unitary variants `.unitaryTwist` and `.unitaryDual` first use the published identities for inclusion of the unitary sublattice. The unitary twist retains exactly the modulus-one hypothesis of the published unitary operation.

The defined maps `Weil.twistExpansion` and `Weil.dualExpansion` act on the fibers of the exact-expansion relation. Given an irreducible lattice element together with its expansion certificate, they return the transformed element with its transported certificate. These maps require a supplied expansion; they do not construct one for an arbitrary exact class.

The proof uses the public theorems `Weil.realizeExact_generator`, `Weil.twistLatticeEquiv_generator`, `Weil.dualLatticeEquiv_generator`, `Weil.includeUnitary_twist`, `Weil.includeUnitary_dual`, `ExactGrothendieckGroup.twist_ofClass` and `ExactGrothendieckGroup.continuousDual_ofClass`. Exactness and continuity of the actual operations are already proved in `ExactTwist` and `ExactDual`; this file supplies their compatibility with `ExactRealization`.
