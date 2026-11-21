# Doubles of divisors of actual polarizations are polarizations

`Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationDoublingDivisionStatement`
is a proposition in an arbitrary universe `u`. It is a statement target, not a
proof.

## Statement

It quantifies the named prerequisite package `P`, a scheme `S`, an actual
abelian scheme `A` over `S`, dual witnesses `W` (the published `DualWitness`
of `PolarizedFiniteLevel`), an actual homomorphism `mu : A ⟶ W.dual P` and a
natural number `k > 0`. If `k • mu` is a polarization in the published sense
`W.IsPolarization P`, it asserts that `2 • mu` is a polarization in the same
sense. Being a polarization means being an isogeny whose fibre at every
algebraically closed point is an ample Mumford map after some extension of the
field.

## Role and provenance

This is an internal target, isolated by Task 3269. The primitive normalized
Harris polarization `HarrisPrimitivePolarization` is an actual map `lam0`
whose positive multiple is the given Harris polarization. The ordinary moduli
functor of `PolarizedFiniteLevel` needs an actual polarization. This statement
makes `2 • lam0` such a polarization. The Library has no theorem that divides
a polarization by an integer.

The factor `2` is chosen because the expected proof uses only constructions
already in the Library and avoids Mumford's division theorem for symmetric
homomorphisms. The divisibility of `k • mu` gives an isogeny property for `mu`
and its symmetry. The Mumford map of the diagonal Poincaré bundle
`(1, mu)^* P` is `2 • mu`; this is proved in the Library for polarizations
(`PolarizationDiagonalMumfordStatement`), and its internal lemmas in
`PoincareDiagonalClasses` require only slice symmetry. Bilinearity of the
Poincaré bundle identifies the `k`-th tensor power of `(1, mu)^* P` with the
diagonal bundle of `k • mu`, which is ample on fibres by
`AmpleMumfordDiagonalStatement`. Ampleness descends from the positive tensor
power by `LineBundle.IsAmple.of_positive_tensorPower_iso`.

The stronger classical statement, that `mu` itself is a polarization, is also
true. It is not asserted here.
