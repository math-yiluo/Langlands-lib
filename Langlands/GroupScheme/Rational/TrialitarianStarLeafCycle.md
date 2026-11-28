# The leaf cycle over a cyclic cubic splitting field

`TitsIndexData.exists_star_leafCycle` takes a `D₄` numbering with centre
`1`, the condition that each leaf has a mover under the star action,
and a degree-three Galois extension. It assumes that the star action
is trivial on automorphisms of the separable closure fixing that
extension. It produces a nonidentity automorphism of the cubic field
and a compatible lift to the separable closure whose star permutation
cycles the leaves in the order `0, 2, 3`.

The Cartan matrix forces the centre to be fixed. Restrict an absolute
automorphism moving leaf `0` to the cubic field. Its restriction is
nonidentity, and its cube fixes the cubic field, so the cubed star
permutation is trivial. The finite permutation calculation identifies
the two possible leaf cycles. Inversion supplies the required
orientation in the second case. `card_three_generator` supplies
generation, the cube identity, and the distinctness of the three
powers from the cardinality of the Galois group.

This gives an explicit lift and numbering for the cyclic diagram
action used in Platonov and Rapinchuk, *Algebraic Groups and Number
Theory* (1994), §6.8, printed pp. 371–372.
