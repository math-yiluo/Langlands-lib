# Scalar identities for finite combinations of Eisenstein seed operators

`scalarSeedOperatorCombination` applies the entries of a free-operator vector to continued scalar seed values. `eventually_scalarSeedOperatorCombination_eq` assumes eventual word covariance and continuation agreement, and a supplied basis-coordinate expansion of the evaluated operator vector. On a common filter it uses linear Eisenstein summation to identify the sum of the operator outputs with the continued combination in those coordinates.

`normalized_seedOperatorCombination_eqOn_of_anchor` applies the scalar continuation identity to the same free-operator vector on a nonempty open anchor. It uses the vanishing zero-operator test to express the normalized operator sum with finite support. This is the form whose derivatives evaluate the actual free-operator Taylor coefficients.

This internal comparison implements the operator identity for the finite normalized holomorphic families in Langlands' proof of Proposition 2, printed pp. 205–207 (Corvallis Part I PDF pp. 200–202).
