# The finite-group Mackey pairing

`mackeyTerm P Q V W w` is the complex dimension of the intertwining space on the stabilizer `Q ∩ w P w⁻¹`, viewed as a subgroup of `Q`. The first action is the restriction of `V` from `Q`. The second action is the restriction of `W` from `P` along conjugation by `w⁻¹`. This internal definition uses the Library's orbit stabilizer and conjugation map to express a summand of the pairing of two induced representations.

`mackeyIntertwiningEquiv` evaluates a map from `V` into the restriction of coinduction of `W` at the inverse of each double-coset representative. The inverse extends a family of maps by the two subgroup covariance laws. If `p w⁻¹ q = p' w⁻¹ q'`, then `q q'⁻¹` belongs to the stabilizer and conjugates to `p⁻¹ p'`. The defining intertwining equation for that coordinate gives the same extended value for both decompositions.

For a finite group, the ordinary induced-character formula and the character formula for intertwining dimensions yield Frobenius reciprocity by reindexing the finite sum by conjugation. The finite induction and coinduction models have the same character. The evaluation equivalence therefore gives `finrank_intertwiningMap_induceRep` by taking the dimension of its finite product of intertwining spaces.
