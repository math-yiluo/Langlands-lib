# Central-factorial relations for compact orthogonal generators

This internal derived unit proves algebraic identities used in the investigation
of actual compact intertwining maps. It uses no external literature assertion.
Let A be any complex associative unital algebra and let X,Y,Z satisfy

- XY−YX=Z;
- ZX−XZ=Y;
- ZY−YZ=−X.

The definition `factor X n` is the sequence D_n(X) given by D_0=1,
D_1=X and D_(n+2)=(X²+(n+1)²)D_n. Scalars act through the complex algebra
structure. `RealCompactPolynomialRelationsStatement` asserts

D_(n+1)(X)Y=(YX+(n+1)Z)D_n(X)

for every natural n, together with the first polynomial braid relation
X(Y²+1)X=Y(X²+1)Y. `realCompactPolynomialRelations` proves the proposition.
The helper lemmas are universe-polymorphic; the packaged statement quantifies
algebras with underlying type in `Type`.

The first-order identity uses only the first two commutators. The implemented
proof establishes a cubic recurrence identity with complex parameter t, then
uses two-step induction. The cases n=0 and n=1 follow by expanding the two
commutators. In the induction step, apply the defining recurrence to
D_(n+3), use the induction hypothesis at n, and apply the cubic recurrence
to obtain (YX+(n+3)Z)D_(n+2). All expansions take place in an associative
algebra; commutativity of X and Y is never assumed.

For the first braid relation, expand XY²X−YX²Y as [Z,YX]. The remaining
two commutators identify this with Y²−X², which is the desired equality.
Lean implements this as a noncommutative linear combination of the three
commutator equalities.

This unit proves neither the general two-parameter polynomial braid nor an
identity of the actual rank-three or rank-four Frobenius crossing words. It
also makes no identification between `factor` and a tail multiplier. Such
identifications require their scalar normalizations and parity signs to be
checked separately. The remaining GL4 kernel-image assertion and the full
two-induction-block filtration are not proved here.
