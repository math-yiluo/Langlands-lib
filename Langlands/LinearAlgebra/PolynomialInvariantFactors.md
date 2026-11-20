# Ordered cyclic factors of a polynomial module

This internal linear algebra argument implements the invariant-factor input to
Arthur–Clozel (1989), Chapter 1, Lemma 1.1, part (i). Mathlib supplies a vector
whose annihilator is the annihilator of the whole module. The Lean proof
constructs a polynomial-linear retraction onto its cyclic submodule using the
Library's balanced nondegenerate pairing on the quotient by the annihilator.

The kernel of the retraction has smaller dimension over the field. Induction
gives its cyclic factors, each of which divides the monic annihilator of the
original module. Prepending that annihilator therefore gives a list ordered
by reverse divisibility.

For uniqueness, an isomorphism preserves the dimension of the kernel of every
polynomial action. In an ordered list the first factor generates the
annihilator, which these kernel dimensions determine. The first factors in
two ordered models thus agree by monicity. Subtracting their contributions
from the kernel dimensions gives the same comparison for the two tails.
Positive degrees distinguish the empty model from any nonempty list.
