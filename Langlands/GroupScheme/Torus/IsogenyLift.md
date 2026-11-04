# Composition of closed-torus lifting up to isogeny

For an actual homomorphism `φ : G ⟶ H` over a field,
`LiftsClosedToriUpToIsogeny φ` means that every actual commutative
torus `S` with a closed subgroup inclusion `i : S.toGrp ⟶ H`
admits an actual commutative torus `T`, a closed subgroup inclusion
`j : T.toGrp ⟶ G`, and an isogeny `f : T.toGrp ⟶ S.toGrp`
such that `j ≫ φ = f ≫ i`. The isogeny is finite, flat and
surjective on underlying schemes. This is exactly the torus-lifting
clause of `SemisimpleIsogenyReductionStatement`.

`TorusIsogenyLiftStabilityStatement.{u}` asserts that this property
holds for identities, is stable under composition, and holds for
central isogenies with affine source. The theorem
`torusIsogenyLiftStabilityStatement` proves this proposition.
All fields and arbitrary field universes are allowed, including
imperfect fields and positive characteristic. Tori may be nonsplit
or have rank zero. Neither the lifting predicate nor its identity
and composition laws impose geometric conditions on the ambient
group schemes. Affineness of the source is explicit in the
central-isogeny case.

## Derived provenance and implemented proof

This is a derived packaging of the actual closed-torus lifting
property and its elementary composition law, with no new literature
assertion.

`liftsClosedToriUpToIsogeny_id` uses the same torus and closed
inclusion and the identity torus isogeny.

For `LiftsClosedToriUpToIsogeny.comp`, lift the prescribed torus first
through the second homomorphism and then through the first. Compose
the two resulting torus isogenies using `IsIsogeny.comp`. Associativity
and the two restriction-square equalities give the restriction square
for the composite ambient homomorphism.

`IsCentralIsogeny.liftsClosedToriUpToIsogeny` is exactly
`IsCentralIsogeny.exists_isogeny_torus_lift` from
`CentralIsogeny.TorusLift`, expressed with the named predicate.

The composition law permits iterating central-isogeny reductions
while retaining actual target-torus lifts. It makes no assertion
that the composite ambient homomorphism is central. This file does
not construct the reductions, prove their termination, or prove
Cartan generation.
