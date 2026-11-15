# First-block Jacquet constituents obstruct left reducedness

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.FirstBlock`.

An internal step of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`: one
direction of the description of left `A`-reducedness through Jacquet modules. It is a
Frobenius-reciprocity argument; the route below (fixed slices, averaging and the right
regular representation of `GL_k`) is internal to this proof and follows no specific
source.

Throughout, `A` is a supercuspidal representation of `GL_d`, `Y` a smooth representation of
`GL_m`, and `LeftReduced F T A Y` is the Library predicate: no irreducible subquotient of
`Y` embeds into a (rank-transported) normalized product `A × σ`.

## Results

* `exists_irreducible_of_hom_ne_zero`: a nonzero morphism `f : Y → X` out of a
  finite-length `Y` yields an irreducible `Z` that is a subquotient of `Y` and a
  subrepresentation of `X`. Proof: `Y / ker f` has finite length and is nonzero; take an
  irreducible subrepresentation of it
  (`SegmentHeadSupport.exists_irreducible_subrepresentation`); it is a subquotient of `Y`
  and embeds into `X` through the injective map `Y / ker f → X`.
* `exists_surjective_of_isSubquotient_supercuspidal` (`0 < d`): an admissible
  representation `ρ` of `GL_d` with `A` as a subquotient maps onto `A`. This is the
  single-block case of the Levi cuspidal constituent theorem
  (`CuspidalSupport.leviCuspidalConstituent_maps` for `oneBlock d`, with the single-block
  Levi identified with `GL_d` by `singleBlockLeviEquivContinuous` and cuspidality by
  `singleBlockCuspidalityClause`).
* `trivialRankZero`: the one-dimensional trivial representation of `GL_0`.
* `not_leftReduced_of_isSubquotient_self` (`m = d`): if `A` is a subquotient of `Y`, then
  `Y` is not left `A`-reduced, because `A` itself embeds into `A × 1` (`1` the trivial
  representation of `GL_0`): `A × 1 ≅ A ⊗ 1` by `binaryRightZeroTensorEquiv`, and
  `a ↦ a ⊗ 1` is injective and equivariant.
* `not_leftReduced_of_jacquet` (`m = d + k`, `0 < d`, `0 < k`): if `Y` has finite length
  and `A` is a subquotient of the first-block restriction of the normalized Jacquet module
  `W = r_{(d,k)}(Y)`, then `Y` is not left `A`-reduced. Proof:
  1. `W` is admissible (`glFiniteLengthAdmissibility`, `Parabolic.isAdmissible_normalizedJacquet`).
  2. `A` is a subquotient of a slice `W^{K}` of vectors fixed by a compact open `K ≤ GL_k`
     (`exists_secondFixedSlice_isSubquotient`); the slice is an admissible `GL_d`
     representation, so it maps onto `A` (previous item), and averaging over `K` gives a
     nonzero `GL_d`-map `φ : W → A` (`exists_ne_zero_of_secondFixedSlice_of_surjective`).
  3. With `σ` the smooth right regular representation of `GL_k` (`rightRegularRep`),
     `exists_external_ne_zero_of_smooth` turns `φ` into a nonzero map `W → A ⊠ σ` of the
     Levi `GL_d × GL_k`.
  4. First adjointness (`Parabolic.FirstAdjointness.equiv`, a linear equivalence) gives a
     nonzero map `Y → i(A ⊠ σ)`, and `i(A ⊠ σ) ≅ A × σ`
     (`SegmentSocleDerivativesProof.nonempty_ofPairProductIso`).
  5. `exists_irreducible_of_hom_ne_zero` gives an irreducible subquotient of `Y` embedding
     into `A × σ`, contradicting left reducedness.

  In the Lean proof the shape `BlockShape.ofPair d k` in the hypothesis is replaced by the
  definitionally equal reducible shape `Shahidi.twoBlocks d k`.
* `not_leftReduced_of_isFirstBlockConstituent` (**first-block criterion**): if `Y` has
  finite length and `A` is a first-block constituent of `Y`
  (`BinaryGeometricPieces.IsFirstBlockConstituent`: either `m = d` and `A` is a subquotient
  of `Y`, or `m = d + k` with `0 < k` and `A` is a subquotient of the first-block
  restriction of `r_{(d,k)}(Y)`), then `Y` is not left `A`-reduced. It combines the two
  previous cases.
