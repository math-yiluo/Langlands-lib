# Formal smoothness of a group-graded fixed quotient

This internal algebraic prerequisite supports smoothness of fixed loci for split-torus
actions on smooth affine schemes. It works with any additive commutative grading group
`M`, not only a rank-one grading. No connectedness, characteristic, or finiteness
hypothesis is imposed on the grading group.

For a ring homomorphism `c : B →+* AddMonoidAlgebra B M`, `fixedIdeal c` is generated
by all coefficients of `c b - single 0 b`. The theorem `fixedIdeal_le_ker_iff` proves
that a ring map from `B` kills this ideal precisely when applying that map to the
coefficients of `c b` gives `single 0 (f b)` for every `b`. Thus this quotient has the
expected fixed-point universal property on algebra-valued points.

The theorem `formallySmooth_quotient_fixedIdeal` assumes that `B` is formally smooth
over `R`, scalars have degree zero, and every coefficient of `c b` is homogeneous
of the indicated degree. It proves that `B / fixedIdeal c` is formally smooth over
`R`. It does not assert that an arbitrary ring homomorphism to a group algebra
arises from a scheme action. The construction and verification of the coaction from
an actual torus action are separate obligations.

The implemented proof uses the square-zero lifting characterization of formal
smoothness. Given a point of the quotient modulo a square-zero ideal `J`, first lift
its composite with `B` to a map `Y` on `B`. All nonzero-degree components map into
`J`. Consequently the degree-zero component of the resulting group-algebra map
is multiplicative: in the coefficient of a product, every off-zero pair of degrees
contributes a product of two elements of `J`. Projection to degree zero therefore
defines a new algebra homomorphism, kills `fixedIdeal c` by homogeneity, and lifts
the original point.

The mathematical context is Milne, *Algebraic Groups* (2017), Theorem 13.1 and
Corollary 13.10, registered source `milne-2017-algebraic-groups`, printed pp.254–257
(PDF pp.270–273). The published errata for Chapter 13 have been checked; the local
ring proof printed there is not the proof implemented here. This square-zero
argument generalizes Worker 1131's rank-one `formallySmooth_quotient_offIdeal`
argument from the shared draft of task `91e60b81-4fc5-4b3f-8ed2-a5accea84f17`,
revision 1. Worker 1131 is a contributing coauthor of that reused argument.
