# The full compact polynomial braid and recursive corner normal forms

This internal unit states a universal algebraic prerequisite as the Prop-valued
`RealCompactPolynomialFullBraidStatement`. It also proves two corner
factorizations and a conditional sufficient criterion. It contains **no theorem
proving the full braid proposition**. That proof is left to separate work.

Let A be any complex associative unital algebra and let X,Y,Z satisfy
XY−YX=Z, ZX−XZ=Y and ZY−YZ=−X. Write D_n(X) for
`RealCompactPolynomialRelations.factor X n`, defined by D_0=1, D_1=X and
D_(n+2)=(X²+(n+1)²)D_n. The full proposition asserts

D_a(X)D_(a+b)(Y)D_b(X)=D_b(Y)D_(a+b)(X)D_a(Y)

for every pair of natural numbers a,b. The packaged statement quantifies over
algebras whose underlying type is in `Type`, with exactly the three commutator
hypotheses above. The helper lemmas are universe-polymorphic. There is no
division or nonzero-divisor premise. The first-parameter-one and
first-parameter-two braids already published in `RealCompactPolynomialBraid`
are the special cases a=1 and a=2. No conclusion for general a,b is drawn from
them.

The normalization lemmas are internal consequences of the published
first-order compact shift relations. Set R(t)=YX+tZ (`corner`). Define the
recursive expressions L_a(t) and T_a(t) by L_0=T_0=1, L_1=T_1=R(t+1), and

- L_(a+2)(t)=[R(t+1)R(t+2)+(a+1)²(Y²+(t+1)²)]L_a(t+2);
- T_(a+2)(t)=T_a(t+2)[R(t+2)R(t+1)+(a+1)²(X²+(t+1)²)].

These are `normalLeft` and `normalRight`. The scalar argument t may be any
complex number. For all natural a,b, `left_factorization` proves
D_a(X)D_(a+b)(Y)=D_b(Y)L_a(b), and `right_factorization` proves
D_(a+b)(X)D_a(Y)=T_a(b)D_b(X).

Both proofs use two-step induction on a, generalizing b, and the
right-hand form D_(n+2)=D_n(X²+(n+1)²) of the recurrence, which holds because
D_n commutes with its generator. For the left corner, expand
D_(a+2)(X)=X²D_a(X)+(a+1)²D_a(X) and apply the induction hypothesis at b+2.
Two applications of the first-order shift give X²D_(b+2)(Y)=D_b(Y)R(b+1)R(b+2).
The right-hand recurrence gives D_(b+2)(Y)=D_b(Y)(Y²+(b+1)²). For the right
corner, write D_(a+2)(Y)=D_a(Y)(Y²+(a+1)²) and apply the induction hypothesis
at b+2. Two shifts give D_(b+2)(X)Y²=R(b+2)R(b+1)D_b(X), and the defining
recurrence gives D_(b+2)(X)=(X²+(b+1)²)D_b(X). Collecting terms yields exactly
the recursive formulas above. The left factorization uses only XY−YX=Z and
ZY−YZ=−X. The right factorization uses only XY−YX=Z and ZX−XZ=Y.

`braid_of_normal_eq` proves the braid for given a,b whenever L_a(b)=T_a(b). It
substitutes the two factorizations and reassociates the products. It never
cancels D_b(X) or D_b(Y), which can be singular in a concrete representation.
Equality of the two recursive expressions is not proved here.

This is an internal algebraic target together with verified supporting
reductions. It cites no external literature. Neither the general braid nor any
application to representations of real groups is asserted as proved.
