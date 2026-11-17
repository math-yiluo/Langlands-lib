# Connected normalizers and central diagonalizable groups

Author: Worker 360.

This internal derived module applies `ConnectedPointedHomFamily` to commutators.
Over any field, let `G` and `H` be affine group schemes with `H` connected, let
`i : D(Λ) → G` be a homomorphism from a diagonalizable group, and let `F` be a
subgroup functor satisfying `range i ≤ F ≤ torusCentralizer i`. If the image of
`h : H → G` normalizes `F`, then it centralizes `i` on every test scheme. Neither
`H` nor `F` is assumed smooth or reduced; `i` and `h` need not be monomorphisms.

`affine_commute_of_connected_normalizer_diagonalizable` proves the assertion on
algebra points. The commutator family sends `(y,t)` to `[h(y),i(t)]`. The conjugate
of `i(t)` by `h(y)` lies in `F`, so every `i(t')` commutes with it. The torus points
also commute with one another. Thus the commutator identity
`[a,bc] = [a,b] b [a,c] b⁻¹` makes this family multiplicative in `t`.
Naturality is functoriality of commutators, and the family is trivial at the
identity of `H`. The connected pointed-family lemma makes it trivial everywhere.

`range_le_torusCentralizer_of_connected_normalizer_diagonalizable` extends this
to all tests. The product of `H` with `D(Λ)` is affine, so an affine presentation
of that product tests universal commutation. Pulling this identity back along
any pair of points proves commutation over every test scheme and every further
refinement, precisely as required by `torusCentralizer`.

`range_le_torusCentralizer_of_connected_normalizer_splitTorus` transports the
same result along an isomorphism `D(ℤ^I) ≅ T` for an arbitrary split torus `T`.
All its hypotheses have the same meaning as above with `T` replacing `D(Λ)`.

These lemmas are internal consequences of the matrix-weight rigidity argument,
not separate translations of a literature statement. Their intended use is the
normalizer clause of Task 6803.
