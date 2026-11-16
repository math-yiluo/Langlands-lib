# Rank-one laws in the supplied coordinates

This internal derived module connects the generic rank-one Weyl calculus
to `LocalSplitCell.RankOneLaws` over a commutative ring. It assumes Weyl
data with affine target and beta equal to one. The coroot must factor as
the fixed-exponent cocharacter of a supplied coordinate torus followed
by a homomorphism into the data's torus. `HasCoordinateCoroot` records
exactly this equality of actual cocharacters.

`cocharPoint_eq_exponentCocharacter` identifies the coordinate definition
of a cocharacter point with evaluation of the actual cocharacter, by the
split-torus point equivalence. `H_eq_cocharPoint` then identifies the
generic coroot values after the supplied torus homomorphism.

When beta is one, the normalized Weyl product is exactly the constant
family of the original three-factor product of the supplied root maps.
The two generic root conjugation results and the square therefore give
the first three clauses of `RankOneLaws`. The arbitrary-coordinate
unit-denominator relation gives its fourth clause, after identifying
the coroot value and associating the products.

All identities hold on every scheme test, including nonreduced tests.
No locality or characteristic restriction is imposed. The beta-one
condition and the supplied Weyl data remain hypotheses; construction for
actual reductive root pairs and the full local Isomorphism Theorem are
separate obligations.
