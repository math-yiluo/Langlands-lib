# Transitivity of arithmetic weak induction in towers

`Langlands.Automorphic.Unramified.WeakInductionTransitivityStatement.{uF,uK,uE,uV,uM,uW}`
concerns actual cuspidal classes `c`, `b` and `d` over number fields in an
algebra tower `E/K/F`. Weak induction of `c` from `b` and of `b` from `d`
gives weak induction of `c` from `d`. The field and presentation universes
are independent, and the two hypotheses use the same universe for the
middle presentations. Their witnesses at that level can differ.

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory
of the Trace Formula* (1989), Chapter III, proof of Theorem 6.2, printed
p. 215, use induction by stages for cyclic extensions to reduce existence
to prime-degree extensions. In the Library weak relation the calculation
only uses actual residue degrees in the unramified Euler polynomials, so
it holds for any tower of number fields.

Compare the two middle spectral witnesses using agreement for presentations
attached to a single cuspidal class. Exclude their exceptional sets, all
ramification, and the contractions of all excluded places in the tower.
For a remaining place `v` of `F`, every place `w` of `E` above `v` has
one contraction `u` to `K`. The polynomial substitutions by `X^f(w/u)`
and `X^f(u/v)` compose to the substitution by `X^f(w/v)`, using
`Ideal.inertiaDeg_tower`. The product over the twice-indexed places is
the product over the places above `v`. Multiplicativity of field degree
also composes the two rank equations. This comparison is about the weak
finite-place relation with genuine spectral attachments.
