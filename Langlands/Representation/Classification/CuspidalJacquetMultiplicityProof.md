# Exact upper and opposite cuspidal Jacquet multiplicities

Authors: Workers 496 and 500.

`Langlands.glCuspidalJacquetMultiplicityPrerequisites.{uF,uV,uW}` proves
exactly the published
`Langlands.GLCuspidalJacquetMultiplicityPrerequisitesStatement.{uF,uV,uW}`.
This is definitionally the complete
`GLCuspidalJacquetMultiplicityStatement`, including both actual normalized
Jacquet modules, their composition lengths, and every irreducible target's
Jordan–Hölder multiplicity. The target pair and its imported files are
unchanged.

The theorem retains every quantifier: an arbitrary prime, actual
`PadicField.{uF}`, supplied topological data, positive rank, associated
ordered block Levis, and an irreducible cuspidal representation on a carrier
in `uV`. Test representations have the independently quantified carrier
universe `uW`. Neither a composition series nor a filtration theorem is a
premise of the final result.

## Implemented proof

The proof first obtains
`CuspidalSupport.associatedJacquetFiltration.{uF,uV} F T n` from the published
`CuspidalSupport.AssociatedProof` module. This is a proof of the full upper
filtration proposition, with no additional premise. It supplies the actual
normalized Jacquet filtration with one graded factor for every
`MinimalConjugatingPermutations B C` index.

For the upper clause,
`glUpperCuspidalJacquetMultiplicityFromFiltration.{uF,uV,uW}` applies this
theorem to the irreducible cuspidal source. That published adapter supplies
the full composition length and all target multiplicity biconditionals.
Worker 500 supplied this adapter; its counting theorem was supplied by
Worker 496.

For the opposite clause, cuspidality supplies smoothness and
quasicuspidality. The proof bundles the source as `SmoothRep.of ρ` and
applies `glOppositeCuspidalJacquetFiltrationFromUpper.{uF,uV}` to the same
proved upper theorem. It obtains an actual `ObjectRepFiltration` of
`CuspidalJacquetMultiplicity.oppositeJacquet T C` of the induced
representation, an equivalence

```text
e : Fin r ≃ MinimalConjugatingPermutations B C,
```

and equivalences from its actual graded quotients to the corresponding
whole-Levi transports of `ρ`. The published opposite transfer constructs
this filtration by block reversal, comparison of the actual coinvariant
quotients, and the exhaustive minimal-index bijection
`v ↦ C.reversePermutation * v`. The present proof reuses that construction.

The family for counting is exactly

```text
w ↦ Rep.of (transport B C w.val.val w.property ρ).
```

`CuspidalSupport.JacquetLength.isIrreducible_transport` proves that every
member is irreducible. Applying `finiteFamilyFiltrationMultiplicity` to
the opposite filtration therefore makes it a genuine composition series
and gives length
`Nat.card (MinimalConjugatingPermutations B C)`.
The same theorem identifies the count of factors equivalent to each test
representation with the cardinality of the matching-family-index
subtype. That subtype is definitionally
`AssociatingPermutations B C ρ τ`. Repeated isomorphic factors retain their
separate indices.

The finite-family theorem supplies a realizing composition series for
each specified multiplicity and uses Jordan–Hölder independence to
exclude every other count. Thus the biconditionals assert existence and
uniqueness of the actual counts. The final proof pairs the upper and
opposite length conclusions and their two multiplicity biconditionals.

## Constructions and provenance

Both branches use the target's actual bundled constructions. Upper
induction has positive half-modulus covariance; upper Jacquet has inverse
half-modulus normalization. Opposite Jacquet is the actual opposite
unipotent coinvariant action with inverse upper full modulus in
`normalizedActionOfModulus`. The published reversal comparison identifies
these precise actions. The proof adds no splitting, semisimplicity,
tensor factorization, dimension hypothesis, Langlands quotient theorem,
or generic relative comparison.

The induced and Jacquet carriers lie in `max uF uV`. Representation
equivalences compare their graded quotients with the source transports
in `uV` and test representations in `uW`, preserving all three independent
universes.

This module is an internal deduction from the published filtration,
conjugation, irreducibility and counting proofs. The original sources for
the unchanged target, already read directly, are Silberger 1979,
Theorem 5.4.1.1, printed pp.287–288
(`silberger-1979-harmonic-analysis`); Bernstein–Zelevinsky 1977,
Corollary 2.13(c) and §2.15(3), printed p.449
(`bernstein-zelevinsky-1977-induced-i`); and Silberger 1978,
printed pp.97 and 100
(`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`).
Their precise source hashes and correspondence are recorded in the
target Markdown. This proof establishes the positive-rank cuspidal
length and multiplicity family stated there; it makes no claim about the
discrete-series maximal tempered part or finer parameter comparisons.
