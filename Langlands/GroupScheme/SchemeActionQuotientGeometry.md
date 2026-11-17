# Geometry of represented free-action quotients

This is a derived construction from the canonical fppf action quotient,
its exact orbit relation for free actions, and descent of scheme morphism
properties. It assumes an actual representation of the quotient sheaf.

The comparison with that sheaf identifies equality of represented classes
with equality in the quotient. Freeness glues the unique difference point
on each original relative test, with no restriction on that test.
For any chosen point of the acted-on scheme, the pullback of the class
morphism along its class is the product with the acting group.
Local surjectivity follows from the canonical quotient map through the
representing isomorphism.

Each point of the represented quotient lies in the image of a member of
the covering sieve of local representatives, so the actual class morphism
is surjective. To retain a scheme morphism property, the proof uses that
same covering sieve on the target. Its pullbacks are the preceding group
products. Any property stable under base change, Zariski local on the
target, and descending along surjective flat locally finitely presented
morphisms therefore descends from the acting group's structure morphism
to the class morphism. The implementation uses the published
`FppfLocal.of_fppfTopology_sieve`. It specializes to flatness,
quasi-compactness (using the published fppf descent lemma), and local
finite presentation.

`GroupIsomorphismScheme.outerOfQuotientRepresentation` applies this
construction to the canonical inverse-precomposition action of a faithful
automorphic action. It takes a representation of its canonical quotient
sheaf and assumes the acting group is flat and quasi-compact over the base.
The class morphism has these two properties and is surjective. Invariance
and the unique difference point on every test follow from the sheaf
comparison and freeness of this canonical action.
The construction does not assert existence of a quotient representation,
separatedness or étaleness of its parameter, or quasi-compactness of either
whole parameter scheme.
