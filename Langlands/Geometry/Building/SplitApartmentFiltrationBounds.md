# Algebraic boundedness of every split apartment filtration

Author: Worker 312.

This is an internal consequence of the actual Chevalley coordinate bounds,
cross-torus transport, split realization and uniqueness of split apartment classes.
It introduces no new assertion from external literature.

`SplitApartmentRootFiltrationBoundedStatement.{u}` concerns a field with its supplied
valuative relation, an affine connected reductive group, a prescribed split maximal
torus, an additive valuation into the extended reals and its real-valued order on
units. It assumes that the two valuations agree on units, that the additive
valuation takes at least three values, and that the valuative relation is the
opposite of the additive valuation order. It also assumes that for every real
threshold there is a nonzero scalar whose additive value is at most that threshold.
For every supplied apartment class, every point of that class, every actual
relative root and every real depth, the actual root filtration is algebraically
bounded in the given group.

The scalar hypothesis is retained explicitly. It is what lets a lower bound on
an additive coordinate valuation produce a nonzero valuative bound at any depth.
No henselianity, completeness or residue-field condition occurs in this statement.

The implementation has four steps.

1. `KPApartmentData.isAlgebraicallyBounded_filtration_of_orbit` writes a point in
   the given translation orbit as a translate of its generating family.
   `rootFiltration_vadd'` identifies the filtration with the generator's
   filtration at a shifted real depth, where the assumed bound applies.
2. `KPApartmentData.isAlgebraicallyBounded_filtration_transport` takes the inverse
   character and a family in the source carrier. The published exact image
   formula for filtrations identifies the target set with the image under the
   actual group isomorphism. Algebraic boundedness is preserved by this
   morphism.
3. `ChevalleyRootFamily.isAlgebraicallyBounded_apartmentFiltration` applies the
   coordinate bound at every depth and the orbit lemma. The existence theorem
   then follows the published split realization: take the root datum of the
   prescribed maximal torus, its Chevalley data and actual Chevalley group,
   identify the tori by their character lattices, and use the published common
   torus isomorphism to transport the bounded apartment to the given group.
4. `KPApartmentData.isAlgebraicallyBounded_filtration_of_isSplitTorus` derives
   additivity of the order on units from the additive valuation and invokes the
   published uniqueness of split apartment classes. It identifies the supplied
   class with the constructed bounded class. The final theorem packages this
   result as `splitApartmentRootFiltrationBounded`.

This proves bounds on every point of a supplied split apartment, rather than
only on the unshifted Chevalley family. Quasi-split torus restriction, field
descent, and the unconditional maximal-unramified target remain separate
obligations.
