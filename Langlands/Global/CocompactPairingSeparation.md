# Nondegeneracy from cocompactness and one-factor approximation

This internal supporting argument works with a field mapped into a commutative
topological ring, a continuous nontrivial additive character trivial on that
field, and compact representatives modulo the field. It also assumes the
one-factor approximation property constructed for actual adeles in
`AdelicLocalApproximation.exists_local_factor`. The field and ring may belong to
independent universes.

`smallParameters` consists of the parameters whose products with the compact
representatives have character values in the open centered circle arc of radius
pi/2. Joint continuity of the pairing and the compact-open topology show that
this is an open neighborhood of zero. A character contained in this arc is
trivial: all positive powers of any of its values stay in the arc, so the circle
small-arc lemma forces each value to be one.

If a small parameter annihilates the field, subtracting a field element puts
every ring element into the compact representative set without changing its
pairing. The whole shifted character then takes values in the arc and is
trivial.

For nondegeneracy, suppose a nonzero parameter annihilates the ring. Choose a
factor e=a*z from one-factor approximation. It also annihilates the ring.
Approximation gives a nonzero field element k such that iota(k)*(1-e) is small.
This parameter annihilates the field, since both the original character and the
e-shift do. The preceding result shows it annihilates the ring. Adding the
e-part proves that iota(k) annihilates the ring. Multiplication by its field
inverse makes the original character trivial, contradicting nontriviality.

This is an internal derivation following Worker 1843's generic proof plan.
It proves nondegeneracy under the explicit approximation assumptions; the
diagonal annihilator identity and surjectivity remain separate obligations.
