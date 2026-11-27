# Elementary Artinian lifting of a pointed abelian scheme

This proves the proposition in `PointedAbelianArtinianLiftingStatement.lean`,
from Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, §6.3,
Proposition 6.15, printed pp. 124–126. The surjective homomorphism is identified
with its kernel quotient, and the supplied abelian scheme is pulled back
to that quotient presentation. The section reduces to the supplied unit.

On a product of affine covers, smoothness of the target lifts the reduced
multiplication locally. The affine comparison implements the lifting torsor
of SGA 1, Exposé III, Proposition 5.1 and Corollary 5.2. The maximal ideal
annihilates the elementary ideal, and translation on the residue group
identifies the differences with tuples of residue-fibre functions. The
source charts are flat, and the Artinian base and smooth residue group
supply the two finite bases for these coordinates.
The two axis restrictions are coboundaries, since the identity map lifts
the restriction of multiplication on either axis. The two-axis Čech lemma
and the elementary correction action glue the local lifts. A constant
correction prescribes the value at the pair of units.

The unit, associative and commutative laws are equalities between pointed
lifts. Their difference functions are constant by smoothness, properness,
and geometric connectedness of the residue-fibre powers. Evaluation at
the sections makes these differences zero. The map `(x, y) ↦ (x, m(x, y))`
is an isomorphism on reduction, and the fibral isomorphism criterion makes
it an isomorphism on the entire family. Evaluating its inverse at
`(x, e)` gives inversion. Geometric connectedness descends along the
surjective residue base change, completing the abelian-scheme structure.
