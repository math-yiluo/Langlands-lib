# Mixed doubled-opposite conjugation coordinates

This internal derived construction proves the two root-coordinate bounds for conjugating an element of `U_{-2a,x,r}` by an element of `U_{a,x,0}`, at positive depth `r`. The full middle-coordinate bound remains an explicit hypothesis of the final coordinate construction.

`mul_double_opposite_mem_block_centralizer_root` applies the proved mixed real-depth exchange to the inverse product. Inverting its factorization and using the original block subgroup puts the negative coordinate of the original product in the complete original block at depth `r`.

`conjugate_double_opposite_mem_root_centralizer_block` proves the positive-coordinate bound. A rank-one normalizer factorization of the ordinary input has opposite factors at depth `-t`, where `t` is its nonnegative valuation. The pure doubled input commutes with the opposite factor on its own side. Normalizer conjugation carries that input to `U_{2a,x,r+4t}`. Real-depth mixed exchange against the remaining opposite factor produces an ordinary coordinate at depth `r+3t` and a doubled coordinate at depth `r+4t`. Both belong to the original full block at depth `r`. The proof also handles an identity ordinary input directly.

`doubleOppositeConjugationCoordinatesOfCentralBound` chooses the ordinary rank-one factorization, initially at half the doubled depth. Uniqueness of the actual opposite-root/centralizer/root product identifies its negative factor with the first bound and its conjugated positive factor with the second bound. The explicit `hcentral` hypothesis places its actual middle coordinate in the original `Z(F)_r`. The result consists of the two original full root blocks, the original centralizer-depth coordinate, and their literal multiplication identity.

`conjugate_double_opposite_mem_moyPrasad_of_central_bound` applies the defining inclusions for those two blocks and the middle image. Thus the explicit middle-coordinate estimate is the only additional input for this mixed conjugation bound.

The proofs use only the supplied apartment axioms, actual rank-one factorization, V4, commutation of the doubled root group with its ordinary root group, and original opposite-cell injectivity. The final construction additionally uses the supplied commutator-friendly filtration and the explicitly stated middle-coordinate bound. They neither prove that bound nor assert unconditional covariance, existence of an open centralizer filtration, or the host simultaneous-basis theorem.
