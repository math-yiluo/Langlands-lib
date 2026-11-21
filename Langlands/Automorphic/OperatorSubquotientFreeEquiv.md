# Descent preserving the full operator action

`Langlands.Automorphic.exists_irreducibleOperatorSubquotient_with_pullbackEquiv`
starts with a surjective map from a common operator monoid to the concrete
automorphic operator algebra. A stable subspace for the pulled-back action
surjects equivariantly onto a specified irreducible model. The numerator
and the kernel are invariant under the concrete operators because every
concrete operator has a lift. The kernel quotient equivalence intertwines
every operator of the common monoid. Invariance of subspaces is the same
under the pullback, so the concrete quotient is irreducible.

`OperatorSubquotient.freeRepresentation` applies this setup to the common
free operator algebra. The comparison with the genuine finite adelic action
uses the finite translation generators. The comparison at each real or
complex place uses the compact inclusion and the enveloping element of the
included complexified Lie generator. The equations for those generators
let the same quotient equivalence transport all the place actions.

This is an internal extension of the operator quotient construction in
[OperatorSubquotientPullback.md](OperatorSubquotientPullback.md). It supports
the descent from Eisenstein coefficients to automorphic subquotients in
Langlands (1979), proof of Proposition 2, printed pp. 205–206 (Corvallis
Part I PDF pp. 200–201), with all the place actions needed for Getz–Hahn
(2024), Theorem 10.7.5, p. 288 (PDF p. 300).
