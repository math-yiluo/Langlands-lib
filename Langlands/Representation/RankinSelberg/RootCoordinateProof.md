# Cumulative-product torus coordinates: proof

`Langlands.RankinSelberg.rootCoordinateChange F T n` proves the published
`RootCoordinateChangeStatement F T n` for every p-adic field `F`, every supplied
topological data `T`, and every natural number `n`. The rank is `n + 1`, so rank
one is included. The field universe is unrestricted. The proof adds no
hypothesis to the target.

The private helper `tail a k` is the product of the coordinates whose indices
are at least `k`. Splitting off its first factor gives `tail_step`; at the end
of the finite index set, `tail_end` is the empty product. The forward map
`diagonalCoords` consists of these tail products, and `rootCoords` consists of
adjacent ratios followed by the final coordinate. The recurrence proves that
taking ratios after tail products recovers the input. Reverse induction on the
index proves the other inverse identity. Finite products give multiplicativity
and continuity, and continuity of multiplication and inversion gives continuity
of the inverse. `coordinateEquiv` packages exactly these maps as a continuous
group equivalence.

For the measure clause, `diagonalCoords_haar` first works in an arbitrary
second-countable, locally compact Hausdorff commutative topological group with
a Borel Haar measure and a measurable subgroup of mass one. Both coordinate
maps preserve the product of this subgroup: finite products stay in the
subgroup, as do adjacent ratios. The inverse identities then identify the
preimage of this product set with itself. The finite product measure assigns
that set mass one. The pushforward by the continuous group equivalence is
Haar, and Mathlib's `Measure.isMulLeftInvariant_eq_smul` identifies it with a
scalar multiple of the original product measure. Evaluating on the product
subgroup forces this scalar to equal one.

The closing theorem applies that lemma to the field's unit group with
`localMultiplicativeHaar` and `integralUnits` of the supplied valuation ring.
It uses the published openness and mass-one lemmas from `Measures`. The
supplied field is second countable by `T.secondCountableTopology`; the embedding
of its units into the field transfers this property. The local-field structure
supplies local compactness and, through its compatible uniform structure, the
Hausdorff property. Thus the measure equality uses the actual supplied topology,
valuation and product measure, with no free normalization constant.

The remaining calculations are finite algebra:

- Interchanging the two products shows that the coordinate `a_i` occurs in
  exactly `i + 1` diagonal entries. The cardinality of the finite lower interval
  gives `prod_diagonalCoords`. Applying the unit-to-field coercion and the
  diagonal determinant formula proves the determinant clause.
- The diagonal matrix multiplication formula scales the last row by its last
  diagonal entry, which `diagonalCoords_last` identifies with `a_(n)`.
- A ratio of tail products with indices `i < j` is the product over the interval
  `i ≤ k < j`. In the product over all positive roots, interchanging three
  finite products counts the occurrences of `a_k`. There are `k + 1` choices
  of `i ≤ k` and `n - k` choices of `j > k`, giving exponent
  `(k + 1)(n - k)`. This is first proved in an arbitrary commutative group as
  `diagonalCoords_modulus`. Applying the monoid homomorphism from field units
  to the real normalized absolute value yields the target modulus formula.

The provenance is the coordinate change isolated in the published statement,
derived from Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions*
(1983), proof of Theorem 2.7, printed pp. 391–392, displays (3)–(6). The Lean
proof implements the elementary inverse, Haar-uniqueness and counting arguments
above; these structural facts are not a separately named source theorem.
This result supplies a coordinate prerequisite. It does not establish quotient
Iwasawa integration, Whittaker expansions, Mellin convergence, rationality,
a common denominator, or the main equal-rank analytic statement.

Source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
printed pp. 391–392.
