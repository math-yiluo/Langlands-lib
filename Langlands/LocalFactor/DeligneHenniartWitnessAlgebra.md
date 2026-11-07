# Algebra of actual Deligne--Henniart witnesses

This internal companion develops algebra on the unchanged actual-object inputs
of `DeligneHenniartStatement`. Worker 1813 authored it.

The existing `CommonClosure.reciprocityUnits_surjective` proves surjectivity of the actual quotient map
followed by the supplied topological isomorphism. `fieldDeterminant` descends
the proved continuous determinant on the continuous exact Grothendieck group
through the closed commutator quotient and transports it by that isomorphism.
Its pullback is the original determinant, by the quotient universal property.
No reciprocity lift or inverse to irreducible-lattice realization is chosen.

The shared `NonabelianSystem.valueAddHom` encodes the existing additive law of a supplied assignment as
an additive homomorphism with target `Additive` of the complex units.
`tensorValueAddHom` composes it with the published continuous bilinear tensor
and the forward exact realization, so negative coefficients are retained.

`exactWitness_iff` and `approximateWitness_iff` replace the universal-lift
relation by evaluation of the descended field character. Surjectivity supplies
a lift for the forward implication; the pullback identity proves the reverse.
The approximate exponent remains after the test representation and Haar
measure. The equivalence makes it independent of the selected lift because
the actual determinant descends, without asserting any uniform exponent.

These are derived algebraic results about the published definitions, not
arithmetic stability assertions or existence of witnesses. The provenance
is the quotient universal property, exact determinant continuity and exact
tensor bilinearity already proved in the imported Library modules.
