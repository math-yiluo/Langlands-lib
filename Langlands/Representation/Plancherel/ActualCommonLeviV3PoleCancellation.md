# Actual compact tensor germs from supplied pole data

The primary construction is
`Langlands.Plancherel.ActualCommonLeviV3.cancelledCompactNumerator`.
It applies finite unitary basis-root cancellation to a supplied polynomial
numerator of the particular actual common-Levi compact tensor. A linear
equivalence of its target compact carrier with a normed complex vector space
lets the cancellation theorem use the supplied cleared bound. Transporting
the quotient back retains the original fixed compact carriers and their
polynomial-operator convention. No topology on those original carriers is
assumed.

The data are explicit: both actual `ContinuedPair` objects, a global
polynomial numerator `N`, a list of root powers in supplied integral bases of
the actual valuation image, a remaining regular denominator `d`, the normed
model equivalence, and a cleared unitary norm bound for the modeled
numerator with denominator `product * d`.

The local-representative theorem further assumes this original denominator
is nonzero on the genuine generic locus and `N = (product * d) * J` there,
where `J` is exactly the published actual compact comparison for those
continuations. It proves the existing `IsLocalRepresentative` predicate for
the canceled numerator and denominator `d` on the ambient open set where
`d` is nonzero. The proof cancels the root product from the two exact
operator identities at each generic point. The canceled numerator is
globally polynomial, and `d` is chosen before any input vector.

If the consumer proves `d` is nonzero at every unitary parameter, the germ
theorem gives the existing `RegularGermAt` at every such parameter. Its
value is the canceled numerator divided by that same `d`. These are
actual regular germs, not values obtained by continuity only along a
unitary subset.

This is a derived assembly step in the cancellation argument of
Waldspurger (2003), Corollary V.2.3 and Lemma V.3.1, printed pp.294–295 /
PDF pp.60–61, registered as `waldspurger-2003-plancherel`. It does not prove
the displayed pole factorization or norm bound for any standard family.
Continuation and scalar-inverse existence, genuine generic density, actual
root support and norm identities, extension intertwining, and all coefficient
and Hermitian preservation identities remain obligations of the closed
target. The field universe and representation-carrier universe remain
independent.
