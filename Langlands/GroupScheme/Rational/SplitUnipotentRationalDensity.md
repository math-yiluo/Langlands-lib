# Dense rational points of split unipotent groups over infinite fields

This helper module serves the proof of
`Langlands.GroupScheme.RelativeRoot.SplitUnipotentStableVectorSubgroupStatement`
(task 6b07dcd2-af39-4c69-8ade-d0faa997a49f). Over an infinite field k, the
rational points of a split unipotent affine group are dense in its underlying
space. This is the classical fact that such a group is an affine space as a
k-scheme. The proof here is topological and was worked out for this
formalization. It uses the Library's density predicate
`Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPoints`: the union of
the images of all rational points Spec k ⟶ X is dense in X.

Everything is in the namespace `Langlands.GroupScheme.RationalDensity`. Fix a
field k and write S = Spec k.

## Sections through rational points

- `pointSection X' x`: for objects X, X' over S and a rational point x of X,
  the section X' ⟶ X ⊗ X' given by lift (toUnit X' ≫ x) (𝟙 X'). The simp lemmas
  `pointSection_fst` and `pointSection_snd` compute its two components.
- `mem_range_pointSection`: a point z of X ⊗ X' whose first projection is the
  image of a point a of S under x lies in the range of `pointSection X' x`.
  Mathlib's `Scheme.Pullback.exists_preimage_pullback` gives a point t of the
  fibre product of x and the first projection over a and z. The image of t
  under the second projection followed by `pointSection X' x` is z. Both
  morphisms into X ⊗ X' agree after each projection of the pullback, by
  `x ≫ X.hom = 𝟙` and the two pullback conditions.
- `dense_iUnion_range_pointSection`: if the first projection X ⊗ X' ⟶ X is
  an open map and X has dense rational points, then the union of the ranges of
  `pointSection X' x` over all rational points x is dense. An open set O of
  X ⊗ X' has open image in X. That image contains the image of some rational
  point x, and then O meets the range of `pointSection X' x`.

## Stability of dense rational points

- `HasDenseRationalPoints.tensor`: if the first projection X ⊗ X' ⟶ X is open
  and X and X' have dense rational points, so does X ⊗ X'. A nonempty open O
  meets some range of `pointSection X' x`, so its preimage under that section
  is a nonempty open of X'. That preimage contains the image of a rational
  point x' of X', and x' ≫ pointSection X' x is a rational point of X ⊗ X'
  whose image lies in O.
- `HasDenseRationalPoints.of_iso`: dense rational points transport along an
  isomorphism over S, by the Library's `hasDenseRationalPoints_of_denseRange`.
- `isOpenMap_fst`: if X'.hom is flat and locally of finite presentation, the
  first projection X ⊗ X' ⟶ X is open. It is the base change of X'.hom, hence
  flat and locally of finite presentation, hence universally open (Mathlib).

## The building blocks

- `hasDenseRationalPoints_of_range_id_eq_bot`: a group H over S whose
  identity has trivial range has dense rational points. Its identity morphism
  equals the constant map 1, so the unit point η is surjective on underlying
  spaces.
- `dense_mvPolynomial_evaluation` and `hasDenseRationalPoints_mvPolynomialSpec`:
  for k infinite, the evaluations at points of kⁿ are dense in the spectrum of
  the polynomial ring k[Xᵢ : i ∈ n]. So that spectrum, as an object over S,
  has dense rational points. These copy the proofs of the Library's
  `dense_polynomial_evaluation_primes` and
  `hasDenseRationalPoints_polynomialSpec`. Those take the variable type in the
  universe of k. The copies take it in `Type`, so that `Fin n` can be used for
  k in any universe.
- `hasDenseRationalPoints_vectorGroup`: for k infinite, the vector group
  `VectorGroup.groupScheme (CommRingCat.of k) n` has dense rational points.
  Its underlying object is the spectrum of k[X₀, …, Xₙ₋₁] over S.
- `hasDenseRationalPoints_of_isVectorGroupOfDimension_one`: the same for any
  one-dimensional vector group, through the isomorphism `hV.iso`.

## Split groups

- `hasDenseRationalPoints_of_hasSplitSeries`: for k infinite, an affine group
  H over S with a split series of length n has dense rational points. The proof
  is by induction on n. For n = 0 the identity of H has trivial range. For
  n + 1, `SplitSeriesDecomposition.HasSplitSeries.exists_iso_tensor` (module
  `Langlands.GroupScheme.Rational.SplitSeriesProductDecomposition`) gives
  K.X ⊗ V.X ≅ H.X, where K has a split series of length n and V is a
  one-dimensional vector group. K.X has dense rational points by induction and
  V.X by the vector-group case. V.X is smooth, hence flat and locally of finite
  presentation over S, so the first projection is open and `tensor` applies.
  `of_iso` transports the result to H.X.
- `IsSplitUnipotent.hasDenseRationalPoints`: for k infinite, a split
  unipotent group H with H.X affine over S has dense rational points.
