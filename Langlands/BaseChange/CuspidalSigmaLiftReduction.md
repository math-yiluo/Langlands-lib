# Conditional supercuspidal σ-lift converse

`cuspidalSigmaLiftExistence_of_descent_and_selfPair` proves
`CuspidalSigmaLiftReductionStatement`. Its premises are
`SigmaDiscreteDescentStatement` and `SigmaLiftSelfPairLFactorStatement`,
both with upper carrier universe `max v uW` for the normalized orbit
product. Its conclusion is `CuspidalSigmaLiftExistenceStatement`, with
independent field universes `u` and `v`, lower carrier universe `uV` and
upper seed universe `uW`. It applies to every cyclic degree.

Choose a common real determinant twist for the upper supercuspidal seed. It
makes the seed unitarizable and preserves the exact period. The period
divides the cyclic degree and is positive. `unitarySigmaOrbitDiscreteness`
supplies admissibility, irreducibility, temperedness, σ-stability and the
exclusion of proper σ-stable inducing Levis for the normalized orbit product.
Applying discrete descent to an intertwiner of that product yields a lower
irreducible admissible square-integrable representation on a carrier in
`Type uV` and a distributional lift with a nonzero scalar.

Realize the two fields as p-adic fields on their original carriers with
their supplied topologies. Use a nontrivial unitary additive character and
a corresponding self-dual measure on each field to obtain the certified
Rankin–Selberg denominators. Enumerate every character of the finite
abelian norm quotient once. Their kernels are open because the norm
subgroup is open.

The upper self-pair denominator has root multiplicity `s` at one because
the `s` unitarizable supercuspidal factors are pairwise inequivalent.
Unitarity puts every root of the upper denominator on the unit circle, so
it is nonzero at `q_E`. The comparison identifies its composition by
`X ^ f` with the product of the lower self-pair denominators. In each lower
pair the smooth dual is twisted by a norm-trivial character through the
determinant. Here `q_E = q_F ^ f` and `f > 0`. Evaluating at `q_F` gives
nonvanishing of the untwisted lower denominator, which forces the lower
segment to have length one. Composition by `X ^ f` preserves the
multiplicity at one, since `X ^ f - 1` has a simple root there. The lower
multiplicities add and each is one exactly when the corresponding norm
twist fixes the supercuspidal representation up to isomorphism. This gives
`Nat.card (normTwistStabilizer E π) = s`.

`exists_cuspidalSigmaLift_of_realPowerTwist` restores the original orbit
product and transports the intertwiner and distributional lift. The inverse
lower determinant twist preserves irreducibility, supercuspidality, the
stabilizer cardinality and the lower carrier. The resulting lift uses the
same scalar supplied by discrete descent.

The mathematical argument specializes Henniart–Lemaire (2011), II.4.12,
Corollaire and Remarque, printed pp. 96–97, using II.4.6(2) and (4),
pp. 88–89, for the two premises, II.3.5(i)–(iii), pp. 80–81, for the
same-field pair factors, and II.2.9, Remarques (4) and (5), pp. 70–71, for
twisting and the use of smooth duals. Arthur–Clozel (1989), Chapter 1,
Lemma 2.8 and Theorem 6.2(b), printed pp. 17 and 51, give the
characteristic-zero σ-discreteness characterization and descent. Chapter 1,
§6.4, Proposition 6.9(i), p. 60, gives the corresponding pair Euler
comparison.
