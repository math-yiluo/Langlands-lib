# Distinct factors and irreducibility of a local Galois orbit product

`not_nonempty_orbitFactorEquiv_of_trivialStabilizer` compares two powers of the cyclic generator below its order. An equivalence of their pullbacks can be pulled back by the inverse of the first power. It then equates the original action with pullback by the second power times that inverse. The resulting automorphism is nonidentity by injectivity of the powers below the order, contrary to stabilizer triviality.

`SigmaOrbitProductIrreducibilityStatement` concerns any finite normalized orbit product of a smooth irreducible unitarizable action on a supplied p-adic topology, for a continuous field automorphism. In `sigmaOrbitProduct_irreducible_unitarizable`, the pulled-back actions are smooth by continuity of the entrywise maps. They are irreducible by invariance under group equivalence and retain the same invariant positive forms. The Library's Bernstein unitary product theorem then gives irreducibility and unitarizability. The proof identifies the general local-field and p-adic normalizations via their equal Levi half characters in the common normalized induction construction.

These lemmas are used in the local sigma-lift route to unique-place supercuspidality. They concern the normalized orbit product itself.
