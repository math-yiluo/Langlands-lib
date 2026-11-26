# Exact Whittaker multiplicity for real character principal series

`RealExactCharacterWhittakerUniquenessStatement` concerns a list of real characters of total rank \(r+1\). For any nonzero real additive scale, every exact Whittaker coefficient map is a scalar multiple of any nonzero exact map for that list and scale. The scalar is independent of the vector and the group element.

The proof uses `exists_standardEvaluation` to represent each map by a continuous Whittaker form on genuine smooth vectors. On a character list, `exists_boundedForm_of_characterEvaluation` gives the corresponding compact-derivative-bounded form on the smooth principal series. The form representing the nonzero coefficient map is nonzero. Smooth Whittaker uniqueness makes the two forms proportional, and evaluating their translates gives the claimed equality of maps.

`uniformModel_ascendingExpand_le_of_ne_bot` applies the result to the ascending character expansion of any rank-correct real block list. If the original exact block model is nonzero, its coefficients pull back along the surjective ascending quotient. Proportionality then puts every ascending coefficient in the original model.

This is an internal consequence of the continuous evaluation and uniqueness results. The smooth uniqueness input corresponds to Casselman, Hecht and Miličić, *Bruhat filtrations and Whittaker vectors for real groups*, Theorem 9.1, p. 184.
