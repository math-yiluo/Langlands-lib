# Compact polynomial braids with first parameter one or two

This module proves two infinite families of exact polynomial
identities in any complex associative unital algebra. It uses the
central-factorial operators D_n(X)=`RealCompactPolynomialRelations.factor X n`,
with D_0=1, D_1=X and D_(n+2)=(X²+(n+1)²)D_n. Suppose
XY−YX=Z, ZX−XZ=Y and ZY−YZ=−X.

`RealCompactPolynomialBraidStatement` states, for every natural n,

- X D_(n+1)(Y) D_n(X)=D_n(Y) D_(n+1)(X) Y;
- D_2(X) D_(n+2)(Y) D_n(X)=D_n(Y) D_(n+2)(X) D_2(Y).

`realCompactPolynomialBraid` proves the proposition. The helper lemmas are
universe-polymorphic; the packaged statement quantifies algebras with
underlying type in `Type`.

The proof first shows that D_n(X) commutes with X, and that evaluation of this
sequence commutes with passing from the opposite algebra to the original
algebra. Applying the previously proved first-order shift identity in the
opposite algebra gives Y D_(n+1)(X)=D_n(X)(XY−(n+1)Z).
Apply that identity with the generators Y,X,−Z and combine it with the
original right shift identity. Associativity gives the first braid family.

For the second family, write R(t)=YX+tZ. Applying each shift identity twice
reduces the two sides to D_n(Y) times, respectively,
R(n+1)R(n+2)+Y²+(n+1)² and R(n+2)R(n+1)+X²+(n+1)²,
followed by D_n(X). The compact commutators imply
[YX,Z]=X²−Y², which makes these two middle expressions equal.
The defining two-step recurrence handles the remaining constant terms.
No division or nonzero-divisor hypothesis is used.

This result covers first parameter one or two only. It does not assert the
general two-parameter polynomial braid, identify this sequence with actual
Frobenius tail multipliers, or compare the full rank-three or rank-four
crossing composites. The scalar normalizations and actual parity signs of
those operators require separate verification. The GL4 kernel-image condition
and the unrestricted two-induction-block filtration are not treated here; the
Library proves that filtration as `realInducedInducedFiltration` in
`RealInducedInducedFiltrationProof`.
