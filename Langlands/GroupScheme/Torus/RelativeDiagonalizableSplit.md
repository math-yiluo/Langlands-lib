# Splitting diagonalizable relative tori

Worker 665. Internal derived construction for Task 7527.

The selected definition `RelativeMultiplicativeType.diagonalizableSplitIso` takes
`S : Scheme.{u}`, an abelian group `M`, a finite type `I`, and an additive equivalence
`b : M ≃+ (I → ℤ)`. It constructs an actual isomorphism
`diagonalizable S M ≅ splitTorus S I`. This construction works over every base scheme,
including the empty scheme. The module groups it with the character-coordinate
constructions and the relative-torus consequence below.

This module constructs finite split coordinates over the original base for an actual
relative torus that is already globally diagonalizable. The main theorem is
`RelativeTorus.IsTorus.isSplitTorus_of_isDiagonalizable`: for `S : Scheme.{u}` with
`Nonempty S` and an actual group scheme `T` over `S`, the published predicates
`RelativeTorus.IsTorus T` and `RelativeMultiplicativeType.IsDiagonalizable T` imply
`IsSplitTorus T`. No rank, geometric connectedness, normality, field hypothesis on the
base, or torsion-free hypothesis on the supplied character group is assumed.

The auxiliary construction `Diagonalizable.characterGroupEquivOfIso` applies the
published field-level diagonalizable full-faithfulness to both arrows of an actual
isomorphism `D(M) ≅ D(N)`. Functoriality and faithfulness turn the two inverse identities
into inverse identities of additive homomorphisms. This gives an additive equivalence
of the full character groups. `characterEquivOfSplitIso` compares the finite split model
with `D(I → ℤ)` and obtains `M ≃+ (I → ℤ)`.

`RelativeMultiplicativeType.diagonalizableSplitIso` uses such an additive equivalence
to construct `D_S(M) ≅ Gm_S^I`. It base-changes the integral diagonalizable splitting
isomorphism and composes with the published split-torus base-change comparison.

For the main theorem, choose one point in the nonempty base and one point above it in
an etale split chart. Pulling the chart's split model back to that point's residue field
exhibits a field splitting of the globally fixed diagonalizable character group. The
preceding constructions recover its finite free coordinates and produce an actual
group-scheme isomorphism over `S`.

Provenance: all constructions and the theorem are internal deductions from the
published relative torus and diagonalizable definitions, the field theorem
`DiagonalizableCharacter.restrictMap_bijective`, and the published diagonalizable and
split-torus base-change comparisons. This helper proves no normal-base isotriviality,
arithmetic cover triviality, or assertion that an arbitrary integer torus is already
diagonalizable. Those are separate inputs to the integer-torus proof.
