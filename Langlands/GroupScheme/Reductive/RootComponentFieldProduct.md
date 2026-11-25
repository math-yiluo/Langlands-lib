# Actual field products indexed by integral Cartan components

The module uses the component-coordinate interface `RootComponentCoordinates`
(`Reductive.RootComponentCentralizerFactors`) and the normal-model interface
`RootPartitionNormalModel` (`Reductive.RootPartitionNormalSubgroup`).

For a supplied `RootComponentCoordinates M`, an algebraically closed field with
an algebra structure over the pinned model's ring, and any supplied normal
root-generated model for each actual Cartan component, this module constructs
an isomorphism from their actual finite product to the actual field pullback of
`M.group`, when that pullback is simply connected or adjoint. Both isomorphisms
restrict along each actual factor inclusion to the prescribed normal-model
inclusion. No particular choice of normal model is required.

First, injectivity of the actual character-lattice equivalence and of the root
indexing shows that distinct component root sets are disjoint. The
component root sets of `Reductive.RootComponentCommutation` already cover
every actual field root, and the pinned
torus becomes a split maximal torus over the field. The generic
`RootPartitionFamily` product isomorphisms therefore apply directly, preserving
their exact inclusion compatibility. The module is an internal specialization
of the field component assembly motivated by Conrad, *Reductive group schemes*
(2014), Proposition 6.4.4 and Remark 6.4.5, pp.232–233.

This proves a field-level product for supplied component models. It does not
assert that these field maps extend to multiplication over an arbitrary ring
or prove the Weil-pair descent statement.
