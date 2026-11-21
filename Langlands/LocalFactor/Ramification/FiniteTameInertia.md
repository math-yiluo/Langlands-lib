# Finite tame inertia

`Langlands.Ramification.Padic.finiteWildInInertia T K` is the first lower
ramification group of the supplied finite extension, viewed as a subgroup
of the zeroth lower group. `finiteTameInertiaQuotient T K` is the quotient
of the zeroth lower group by that subgroup. Here `T` gives the topology,
valuation, and residue field on the upper p-adic field. The definitions use
the actual lower filtration, not an abstract group of the same order.

`FiniteTameInertiaStructureStatement` states that for a finite Galois
extension of p-adic fields, with residue characteristic `p`:

- the first lower group is a `p`-group;
- the tame quotient admits an injective homomorphism to the multiplicative
  group of the residue field of the upper field;
- the tame quotient is cyclic, and its order divides the residue cardinality
  minus one and is prime to `p`.

The statement is at independent universes for the two fields and is not a
claim about the absolute tame quotient or the action of Frobenius on it.

**Source.** J.-P. Serre, *Local Fields* (1979), IV §2, Proposition 7 at
index zero and Corollaries 1 and 3, printed pp. 67–68 (PDF pp. 74–75),
registered as `serre-1979-local-fields`. The divisibility assertion expresses
Lagrange's theorem in the finite residue unit group. Only the indicated
parts of the source results are stated here.
