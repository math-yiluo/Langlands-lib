# Real standard-module parameters in a common isotypic module

Two rank-correct lists of real blocks give standard modules of
`GL_n(ℝ)`. Suppose that their `O(n)`-finite functions admit injective
intertwiners into a common module. Suppose that this module is spanned
by images of intertwiners from one irreducible admissible
\((\mathfrak{gl}_n(\mathbb R),O(n))\)-module. Then the normalized block
data of the two lists agree up to permutation. The common module can
have arbitrary multiplicity. The statement leaves the order of both
input lists free and keeps the two carrier universes independent.

The data are `realMoeglinData`. A real character contributes its parity
and exponent. A nonzero-weight induction block contributes its
absolute weight and exponent, which label the corresponding twist
of a discrete series of `GL_2(ℝ)`. A weight-zero induction block is
expanded into the two real characters of the same exponent with
opposite parities. See Knapp (1994), (2.1)–(2.4), pp. 399–400
(one-based PDF pp. 409–410), and the weight-zero description on p. 402
(one-based PDF p. 412). The standard-module normalization is documented
in `StandardModule.md`, Derived choices 2–4.

This formulation is derived from Tadić (2009), Propositions 1.1 and
1.3, pp. 6–7 of the author's PDF. Proposition 1.1 makes the virtual
classes of the normalized inductions independent of block order.
Proposition 1.3 makes these standard classes a basis indexed by the
multisets of essentially square-integrable inducing factors. The
embeddings imply that both standards are isotypic for the same simple
type. They have finite length and are nonzero for rank-correct data, so
their virtual classes are positive integer multiples of the same
irreducible class. Two distinct standard basis elements cannot be
proportional. The equal multisets of inducing factors are the required
permutation of normalized data. For rank zero the two lists are empty.
