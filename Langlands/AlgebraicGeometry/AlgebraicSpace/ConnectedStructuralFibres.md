# Structural connected fibres and geometric component counts

This internal supporting unit connects the actual morphism predicate
`HasGeometricallyConnectedFibres` to the actual component count used in the
geometric-component constructibility statement. The full limit-descent theorem
remains open.

`componentCount_eq_one_iff_connectedSpace` is a general topological fact with
nonemptiness included: cardinality one of the connected-component quotient
means that quotient is a nonempty subsingleton. Its surjection from the original
space gives nonemptiness. Equality of every pair of component classes then
makes every connected component the whole space, proving preconnectedness.
Conversely a nonempty connected space has a nonempty subsingleton component set.

`basePresheafIsTerminal` applies preservation of terminal objects by the lifted
Yoneda functor to the terminal object of the relative scheme category.
`structuralMorphism` is its unique map from the given space.
`structuralFibreIso` uses the product universal property over a terminal target
to identify its actual presheaf fibre with the product with the represented test.
The point homeomorphism of this isomorphism proves
`hasGeometricallyConnectedFibres_structural_iff`, with all fields in the original
universe and their arbitrary structure maps to the base.

For an arbitrary commutative ring B,
`hasGeometricallyConnectedFibres_structural_iff_componentCount` assumes exactly
`FinitePresentationOverRing B X`: a surjective etale atlas locally of finite
presentation and quasi-compact over Spec B. It does not assume
quasi-separatedness, Noetherianity or constructibility. The forward implication
tests the canonical algebraic closure of each residue field. The converse uses
the algebraically closed field-test criterion, and
`GeometricComponentTransport.geometricFibreEquiv` compares that test's actual
component set to the canonical one at its underlying ordinary point. The atlas
supplies the locally finite type and quasi-compact hypotheses of that comparison.
The general topological fact and the actual structural fibre isomorphism finish
the proof. Thus count one includes nonemptiness, in agreement with the published
morphism predicate.

All constructions and proofs are derived from existing Library definitions,
point homeomorphisms and component-transport theorems and Mathlib's terminal,
connected-component and cardinality facts. No additional external assertion is
introduced. The unit provides a criterion, not eventual vanishing of the bad
locus or the connected-fibre clause of `SpaceLimitPropertyDescentStatement`.
