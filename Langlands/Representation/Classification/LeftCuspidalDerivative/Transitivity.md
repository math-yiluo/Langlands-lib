# Transitivity of first-block Jacquet constituents

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Transitivity`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. It proves
that the relation `IsFirstBlockConstituent` (defined in
`BinaryGeometricPieceConstituentsStatement`: `ρ` on `GL_a` is a subquotient of `Y`, up to
rank transport, or of the restriction to the first block `GL_a` of the normalized Jacquet
module of `Y` along the two-block shape `(a, k)`) is transitive for irreducible
constituents of a finite-length representation. This is the transitivity of Jacquet
functors (Bernstein–Zelevinsky 1977, Proposition 1.9(c)) read on subquotients. The proof
uses the Library's ordered Jacquet occurrence lemmas for three-block shapes; no hypothesis
beyond those in the Lean statements is used.

## Declarations

* `exists_family_of_isSubquotient_block`: let `Y` on `GL_m` (`m > 0`) have finite length,
  `D` a block shape and `ρ` an irreducible subquotient of the restriction of
  `r_D(Y)` to the block `j₀`. Then there is a family `X` of irreducible admissible
  representations of the blocks of `D` with `X j₀` equivalent to `ρ` and the external
  tensor product `⊠ X` a subquotient of `r_D(Y)`. Proof: `r_D(Y)` has finite length
  (`Parabolic.normalizedParabolicFiniteLength`); the restriction to the block preserves short
  exact sequences (`restrictionFunctor`, module `PieceTools`; finite length of the restriction
  is neither claimed nor needed), so `ρ` is a subquotient of the
  restriction of an irreducible subquotient `Z` of `r_D(Y)`
  (`exists_irreducible_of_isSubquotient_map_of_finiteLength`). `Z` is admissible
  (`CuspidalSupport.irreducibleLeviAdmissibility`) and factors as an external tensor
  product `⊠ X` of irreducible admissible representations
  (`CuspidalSupport.padicLeviAdmissibleFactorization`). The restriction of `⊠ X` to the
  block `j₀` has only constituents equivalent to `X j₀`
  (`isSubquotient_factor_of_external_comp_mulSingle`), and irreducible subquotients of an
  irreducible representation are equivalent to it
  (`CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient`).
* `isSubquotient_singleBlock_jacquet`: for a one-block shape `D` of `GL_n`, the external
  tensor product of the rank-transported `Y` is a subquotient of `r_D(Y)` (it is
  equivalent to it, `T.singleBlockNormalizedJacquetTensorEquiv`).
* `threeBlockFactors`: the family `(A₀, A₁, A₂)` on the blocks of the three-block shape
  `Parabolic.threeBlocksRight b l k`, of total rank `(b + l) + k`.
* `isSubquotient_of_oneBlock`: if `⊠ Z` is a subquotient of the Jacquet module of `X`
  along the one-block shape of `GL_b`, with `Z` irreducible, then `Z 0` is a subquotient
  of `X` (from `isFirstBlockConstituent_of_isSubquotient_jacquet`, module `Pieces`; the
  alternative with a second block is impossible by rank count).
* `isFirstBlockConstituent_trans_main`: the case `b, l, k > 0`. Let `ρ` (on `GL_{b+l}`) be
  an irreducible subquotient of the first-block restriction of `r_(b+l,k)(Y)`, and `σ`
  (on `GL_b`) an irreducible subquotient of the first-block restriction of `r_(b,l)(ρ)`.
  Then `σ` is a first-block constituent of `Y` along `(b, l + k)`. Proof:
  1. By `exists_family_of_isSubquotient_block`, `X 0 ⊠ X 1` is a subquotient of
     `r_(b+l,k)(Y)` with `X 0 ≃ ρ`, and `Z 0 ⊠ Z 1` a subquotient of `r_(b,l)(X 0)` with
     `Z 0 ≃ σ`.
  2. With the bracketing `((b, l), k)` (`Parabolic.rightRefinement`,
     `Parabolic.rightLabelEquiv`), `Parabolic.subquotient_orderedJacquet_of_coarse_factors`
     gives `Z 0 ⊠ Z 1 ⊠ X 1` as a subquotient of the three-block Jacquet module
     `r_(b,l,k)(Y)`; in the second coarse block the one-block Jacquet module of `X 1` is
     `X 1` itself (`isSubquotient_singleBlock_jacquet`).
  3. With the bracketing `(b, (l, k))` (`Parabolic.leftRefinement`,
     `Parabolic.leftLabelEquiv`, coarse shape `(b, l + k)`),
     `Parabolic.exists_factorized_coarseJacquet_of_ordered` gives irreducible `X'` with
     `X' 0 ⊠ X' 1` a subquotient of `r_(b,l+k)(Y)` and the one-block Jacquet module of
     `X' 0` containing `Z 0`; hence `Z 0`, and so `σ`, is a subquotient of `X' 0`
     (`isSubquotient_of_oneBlock`).
  4. `X' 0` is a first-block constituent of `Y`
     (`isFirstBlockConstituent_of_isSubquotient_jacquet`), and first-block constituents
     are closed under subquotients (`isFirstBlockConstituent_of_isSubquotient`).
* `isFirstBlockConstituent_trans`: if `Y` has finite length, `ρ` and `σ` are irreducible,
  `ρ` is a first-block constituent of `Y` and `σ` one of `ρ`, then `σ` is a first-block
  constituent of `Y`. The cases where one of the two relations is the subquotient
  alternative follow from transitivity of subquotients and from exactness of the Jacquet
  functor on subquotients (`CuspidalSupport.normalizedJacquetSubquotient`); the remaining
  case is `isFirstBlockConstituent_trans_main`.
