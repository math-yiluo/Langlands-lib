# Constant outer charts for two pinned split reductive models

`PinnedOuterIsomorphismChartStatement.{u}` is an unproved local geometric
prerequisite. Two supplied `AffinePinnedModel`s are pulled back to an arbitrary
common scheme `S`. For every supplied full-centre relative adjoint quotient of
the source and every supplied all-test isomorphism-scheme representative, the
statement asks for a type `D : Type u` and an actual family of isomorphisms
parametrized by the disjoint union of `D` copies of `S`.

The family is required to give a bijection on every relative scheme test:
an isomorphism is uniquely an adjoint point acting on one point of that constant
parameter scheme. The action is the existing inverse-precomposition action
`GroupIsomorphismScheme.actionHom hq.innerAction`. Its adjoint point lies on
the original test. No lift to a point of the source group is assumed.

The parameter is `Over.mk (Sigma.desc (fun _ : D => 𝟙 S))`. The coproduct is
taken in schemes, so its points over a test scheme allow locally varying labels
in `D`. The statement does not assert that one label describes an arbitrary
disconnected test. The base and tests may be disconnected, nonaffine, nonreduced
or empty. No finiteness or nonemptiness condition is imposed on `D`, and the
statement does not specify an identification of `D` with root-datum comparisons.
In particular, it retains the possibility of infinitely many outer components
for tori.

This is a derived selection from Brian Conrad, *Reductive group schemes*
(2014), Theorem 6.1.17, printed/PDF p.197, and Theorem 7.1.9(3) with its
all-test sheaf argument on printed/PDF pp.245–246. The pinned isomorphism theorem
provides representatives of the based-root-datum comparisons between the two
split models. The automorphism splitting gives the unique adjoint discrepancy.
On arbitrary tests the root-datum comparisons vary locally; their constant
scheme, rather than a single fixed comparison, records this variation.
Changing from conjugation to inverse precomposition inverts the adjoint
coordinate and preserves the asserted bijection. The empty-base extension is
trivial. These are explanations of the intended derivation, not a proof supplied
by this module.

The scope is a split local chart for a pair of supplied models. It does not
assert general automorphism representability, construct the supplied models or
adjoint quotient, or prove the generic DVR outer-isomorphism existence statement.
Together with the product construction from an all-test bijection, such a chart
would give an outer quotient whose parameter is this constant scheme.
Separatedness, étaleness and local quasi-finiteness of a constant scheme are
separate general geometric consequences needed for descent; no proof of those
consequences or of this statement is included here.
