# Finite character expansions of twisted induced distributions

Let `G` be a locally compact Hausdorff totally disconnected topological
group with a left-invariant Borel measure finite on compact sets. Let `P`
be a closed subgroup with compact `P \ G`, preserved by a finite-order
automorphism `θ` of `G` with continuous forward and inverse maps. Let
`p : P → M` be a continuous homomorphism equivariant for the action on
`P` and an automorphism of `M`. Fix an inducing representation `Ξ` of
`M`, a twisting isomorphism on `Ξ`, and a compactly supported locally
constant test on `G`.

Assume the inflated inducing representation `Ξ ∘ p` is admissible. For
each invariant unramified character of `M` whose twisted induction is
admissible, the actual twisted trace is a finite linear combination of
character evaluations. The coefficients are independent of the character.
This is the trace regularity calculation of Rogawski (1988), Lemma
11.1(a), and Henniart–Lemaire (2011), II.5.7.

Choose an invariant compact open level of bi-invariance for the test. The
fixed space of the induced representation is the product of the coefficient
fixed spaces at a finite double-coset transversal. Each stabilizer is
compact because `P` is closed and the level is compact. Its image under
`p` is compact by continuity, so every allowed unramified character is
trivial there. Admissibility of `Ξ ∘ p` gives finite-dimensional
stabilizer fixed spaces. The evaluation model uses one basis for all
allowed characters.

The twisted trace is the trace of the test operator composed with the
twisting operator on this fixed space. On fixed vectors the test operator
is a finite sum of translations. In a translated twisted section, the
evaluation at each representative applies the inducing isomorphism to a
value of the original section at the inverse-automorphism image of the
translated point. Write that point as a parabolic element times a
representative times an element of the level. Covariance contributes one
evaluation of the unramified character at the projected parabolic
element. Summing with the fixed-model basis coordinates yields the
coefficients of the trace.

`exists_finiteLaurentEvaluation_of_characterCoefficients` turns such a
finite expansion into a Laurent polynomial for any parameterization in
which character evaluation is a monomial with integral exponents. In a
standard Levi of a general linear group, the exponents can be taken to be
the determinant orders of the blocks.
