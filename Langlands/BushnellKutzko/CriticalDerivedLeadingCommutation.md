# Commutation one step beyond a filtration degree

This internal helper for BK93 (2.4.1)(iii) formalizes the commutation tests used in the cyclic-lift argument. For fixed `x`, the test at degree `j` is the integral submodule of endomorphisms `y` with `y*x - x*y` in filtration `j+1`. The test alone does not impose that `y` belongs to filtration `j`.

The multiplication lemma uses the commutator product rule and takes the filtration memberships of both factors at their respective degrees as separate inputs. Inversion uses the commutator conjugation identity and the inverse's opposite degree. Natural and signed powers then follow by iteration and inversion. The submodule structure permits degree-matched addition and integral scalar combinations.
