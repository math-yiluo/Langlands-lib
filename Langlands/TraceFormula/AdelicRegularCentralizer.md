# Commutativity of regular rational adelic centralizers

`AdelicRegularCentralizerStatement` supplies the commutativity of the
centralizers of the rational classes that occur in the ordinary and
twisted simple trace formulas. The ordinary class has a regular
elliptic component at a finite place. In the cyclic Weil restriction
case the same condition is imposed on the ordered norm at a finite
place upstairs. The twisted assertion takes
`GeneralLinearWeilAdelicTwistStatement` as input.

A regular semisimple rational matrix stays regular semisimple after
scalar extension to every completion. Elements commuting with that
matrix after embedding into the adeles commute at each place, by
commutativity of the local regular centralizer. Equality of all
matrix entries at all places gives commutativity in the adelic
matrix group. Regular ellipticity at one finite place supplies
separability of the rational characteristic polynomial.

For the twisted assertion the Weil comparison transports the ordered
norm of the given rational point to the diagonal image of the
matrix norm. Every twisted centralizer element commutes with the
ordered norm, by telescoping through the factors and using the order
relation of the Galois automorphism. The same adelic matrix argument
therefore proves commutativity of the actual norm-one twisted
centralizer.

This internal lemma gives the commutativity needed for compatible
orbital measures in the geometry of Arthur–Clozel, Chapter 1,
Lemma 1.1 and Theorem 4.5. It uses the ordinary centralizer of the
norm for that purpose.
