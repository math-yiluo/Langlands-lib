# Residue degrees and norm pullback of real twists

`exists_pos_residueDegree` uses the map of the actual residue fields induced by the relative field embedding. Its degree is positive and their finite cardinalities satisfy `q_E = q_F^f`, the relation used in `IsResidueDegree`.

`realPowerCharacter_comp_relativeNorm` applies `normalizedAbs_relative_norm` on units and then takes the same real power over both fields. Thus an unitarizing determinant twist can be removed with the same exponent on the lower and upper fields in a σ-lift. Both results use the supplied p-adic topological data on the field carriers.
