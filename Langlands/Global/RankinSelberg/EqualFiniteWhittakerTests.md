# Finite equal-rank tests on the presentation components

This internal module combines the Library's local genericity and p-adic
nonvanishing theorems with the exact linear equivalence from each
presentation factor to its embedded local representation.

`exists_tests` takes two presentations with irreducible admissible finite
components, a nontrivial additive character of the p-adic completion at the
chosen place, and a self-dual measure. The published cuspidal local
functional gives genericity for each prescribed character using the
integer-trivial character comparison. The first character is the given
character. For the second, scaling by `-1` gives its inverse standard
unipotent character. The published `padicEqualNonvanishingTest` then gives
one `EqualLocalTestData` on the two embedded representations whose ordinary
and dual integrals are each nonzero at some point of every right
half-plane. The test data use the canonical p-adic topology.

`FactorCoefficient` bundles a factor functional, a reference vector of
functional value one, and a vector whose coefficient is exactly a specified
function on the local group. `factorCoefficient` pulls back the embedded
functional along the presentation equivalence and chooses the latter two
vectors using the normalized-vector and prescribed-model constructions in
`FiniteWhittakerModelAssembly`.

`inverse_factorCharacter` identifies the standard unipotent character
formed from `inverseFinite` with `Whittaker.inverseStandardCharacter`.
The proof checks the underlying complex values after evaluating both
characters on a unipotent element. `inverseComponentFunctional` transports
the second test functional through this equality. To preserve the second
coefficient function, `exists_inverseModelVector` lifts it to an actual
representation vector by `modelMap_surjective` and takes that vector's
coefficient for the transported functional. Evaluation agrees at each
group point because the transport preserves the underlying linear form.
`inverseFactorCoefficient` applies the factor construction to this
function, with the resulting exact value identity for the original test.

`pair_invariant` uses the defining covariance of each coefficient-model
vector. The standard character takes values in complex units and the second
factor uses its inverse, so the product descends to the local left quotient.
