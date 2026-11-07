# Finite additive conductors from the actual adelic pairing

Worker 1692, derived support for the actual Hecke global functional equation.
The module proves the finite-support consequence of an actual topological
multiplication-pairing equivalence. Its existence is an explicit hypothesis
and is not established here. All conclusions retain an arbitrary number field
in universe `u` and every supplied local component family satisfying
`IsFiniteAdditiveComponent`.

A compact set of actual adeles is integral at almost every finite place,
uniformly over the set. The proof covers it by translates of the open integral
finite-adele subgroup and takes a finite subcover. Each of the finitely many
representatives is integral almost everywhere by the restricted-product
definition, so the same finite exceptional set works for the whole compact set.

At a supplied local p-adic topology, an inverse uniformizer is not integral.
If the actual additive conductor is at least one, the character is trivial on
every product of an inverse uniformizer with an integer. Both assertions use
the specified discrete valuation and actual conductor specification.

`conductorProbe` is the adele supported at one finite place, with coordinate the
inverse uniformizer when that place's additive conductor is at least one, and
zero otherwise. `conductorProbe_pairing_eq_one` proves its pairing with any adele
integral at that place is one. The proof uses the supplied component's exact
restriction identity and the local conductor calculation.

For `eventually_additiveConductor_nonpos_of_pairing`, consider the family of
characters corresponding to these probes under the supplied equivalence.
On each compact subset of the adele group they eventually equal the trivial
character, by the uniform integrality lemma. The compact-open neighborhood
criterion therefore makes them converge to the trivial character along the
cofinite filter on finite places. Continuity of the inverse equivalence makes
the probes converge to zero. The set of adeles integral at every finite place
is an open neighborhood of zero, so the probes are eventually integral.
A positive-conductor probe is not integral at its chosen place; hence the
conductors are eventually nonpositive.

`eventually_additiveConductor_nonneg` uses continuity of the global character
and the published finite integral-support theorem, without a duality
hypothesis. Integral triviality of each supplied component gives conductor at
least zero by the intrinsic conductor's maximal-level property.
`eventually_additiveConductor_eq_zero_of_pairing` combines the two inequalities.
`exists_finset_additiveConductor_eq_zero_of_pairing` expresses the result with
an explicit finite exceptional set.

Finally, `exists_finset_finiteEpsilon_eq_one_of_pairing` applies the existing
finite-epsilon support theorem to this additive exceptional set and to finite
ramification of the actual Hecke character. It proves the exact finite epsilon
expression is one outside a finite set, for every complex spectral parameter
and every supplied family of self-dual Haar measures.

This is derived support for Weil, *Basic Number Theory*, second edition (1973),
IV.2, Corollary 1, printed pp.69–70 (PDF pp.86–87). Weil uses the duality of
open and compact annihilator subgroups. The implemented proof instead uses
compact-open convergence of the inverse-uniformizer probes and continuity of
the inverse equivalence. The hypotheses still require the full actual
topological pairing, not merely an algebraic bijection. The module proves
neither its existence nor the analytic global functional equation.
