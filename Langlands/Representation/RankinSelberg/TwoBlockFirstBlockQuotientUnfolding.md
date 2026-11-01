# Normalized first-block orbital restriction and block measure unfolding

These are derived measure-theoretic helpers for the existing first-block quotient integration target, over every canonical p-adic field and positive two-block shape. They use the actual left quotients and the specified Haar measures. They establish no first-block disintegration identity.

`small_orbitKernel_comp_zero` assumes compact-test compatibility of a small quotient measure with the general linear and upper-unipotent Haar measures. Its conclusion identifies the orbital kernel composed with the quotient measure restricted to determinant slice zero with the pushforward of `normOneHaar`. Left multiplication by an upper-unipotent element fixes both the quotient point and its determinant order. Consequently the orbital kernel is supported on the fiber of the quotient projection, and an indicator calculation restricts the full measurable Weil formula to the zero slice. The preimage of this slice is exactly the norm-one subgroup. The exact equality `map_normOneHaar` then supplies the restriction normalization, with no scalar.

`lintegral_blockHaar` unfolds the specified block-unipotent measure for every measurable nonnegative extended-real function. The definition is the pushforward of the dependent product of the two unipotent Haar measures through the existing block equivalence. The measure-preserving equivalence between a dependent product over `Fin 2` and the binary product, followed by Tonelli, gives the displayed iterated integral in first-block then second-block order.

The indicator-restriction argument follows the published `TwoBlockUnipotentQuotientTower.comp_restrict_eq_smul` of Worker 235; the groups and normalization here are those of the first-block problem. These lemmas are internal consequences of the existing Library constructions rather than additional source assertions.

`SmallOrbitKernelRestrictionStatement` is a proposition-valued abbreviation for the conditional small-slice measure identity. The immediately following theorem proves that assertion explicitly; the block-unfolding lemma is supporting infrastructure in the same focused unit.
