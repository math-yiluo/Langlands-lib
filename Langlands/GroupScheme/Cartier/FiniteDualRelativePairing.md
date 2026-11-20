# Actual relative characters from the finite dual pairing

For a cocommutative finite projective commutative Hopf algebra `A`,
`schemePairing` evaluates the algebraic pairing on the relative global
sections of a test scheme. The Hopf spectrum point equivalence supplies
both algebra points. The point equivalence for the multiplicative group
converts the resulting unit to an actual scheme point. The construction
respects multiplication in each point and restriction along maps of
test schemes.

For a dual point `y` on a test `T`, the pairing on every `V → T` uses
the restriction of `y` to `V`. This family is a natural transformation
of the restricted group-valued point functors. The relative Yoneda
comparison turns it into the actual homomorphism `characterOfPoint y`
after pullback to `T`. Evaluating at the identity map of `T` recovers
the Library's `evaluation` map, as seen by the two projections of
the pullback. Pointwise multiplication makes the character comparison
a natural transformation of additive group-valued presheaves.

`schemePairing_bidual` identifies the two evaluations by the
double-dual coordinate equivalence. It follows from the symmetry of
the algebra pairing and naturality of the relative spectrum adjunction
in its coordinate algebra.

This applies the coordinate pairing in Demazure and Gabriel,
*Groupes algébriques*, Tome I (1970), Chapter II, §1, no. 2, 2.10(a)
and 2.10(d), printed pp. 156–158, to the Library's actual relative
homomorphisms.
