# Constituents of one block of a geometric piece

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.PieceStructure`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. It belongs to the
analysis of the pieces of the geometric lemma (Bernstein–Zelevinsky 1977, §2.12 and Theorem
5.2). This is where the piece filtration of `r_C ∘ i_B` meets products of
representations. For one piece and one block of the target shape, it describes every
irreducible constituent in terms of irreducible factors on the flattened source refinement.
The module states nothing beyond the Lean statements below. Every fact used comes from the
Library or from the earlier internal modules `PieceTools` and `PieceTransport`.

## Finite length

* `hasFiniteLength_externalSmoothObject`: for `0 < n`, a block shape `B` of `n`, and a
  family `Y` of finite-length smooth representations of the blocks `GL_{B.size i}`, the
  external tensor product `FiniteTensor.externalSmoothObject Y` (a representation of the
  Levi `B.Levi`) has finite length.
  Proof: every finite-length representation is admissible (`finiteLengthAdmissibility`).
  Each `Y i` matches itself (`ProductLengthProof.selfMatching_of_finiteLength`), so
  `FiniteTensor.padicExternalTensorFactors` supplies a composition series of the external
  tensor. `LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength` then gives
  finite length.

## Bridge

* `refinedInductionObjEquiv`: the action on an object `σ` of
  `T.normalizedRefinedInductionFunctor C R` is equivalent (by `Representation.Equiv.refl`,
  since both sides are definitionally equal) to `T.normalizedRefinedInduced C R
  σ.representation`. This is a separate declaration because checking that definitional
  equality inside the main proof is too expensive.

## Structure theorem

* `exists_factors_of_isSubquotient_geometricPiece`. Data:
  * `0 < n`, block shapes `B`, `C` of `n`;
  * a minimal representative `w` (`Geometric.IsMinimalRepresentative B C w`);
  * intersection refinements `S` of `B` and `R` of `C`, with `hS : sourceLevi B C w =
    refinedLevi B S` and `hR : sourceLevi C B w⁻¹ = refinedLevi C R`;
  * a family `Y` of finite-length representations of the blocks of `B`;
  * a block index `j₀` of `C`;
  * an irreducible representation `ρ` of `GL_{C.size j₀}`.

  Hypothesis: `ρ` is a subquotient of the restriction, along `MonoidHom.mulSingle _ j₀`, of
  the geometric piece `(geometricPieceFunctor T B C w S R hS hR).obj (externalSmoothObject Y)`.

  Conclusion: there is a family `X` of representations of the blocks of the flattened
  refinement `B.flatten S` with the following properties:
  1. every `X k` is irreducible and admissible;
  2. for every block `i` of `B`, the regrouped tensor
     `Parabolic.flattenedBlockTensor T B S X i` of the factors in the sub-blocks of `i` is a
     subquotient of the normalized Jacquet module `(T.normalizedJacquetFunctor (S i)).obj (Y i)`;
  3. `ρ` is a subquotient of the normalized parabolic induction along `R j₀` of
     `Parabolic.flattenedBlockTensor T C R X' j₀`. Here `X' k` is the rank cast
     `T.castRank (size_blockEquiv_symm hw k) (X ((blockEquiv hw).symm k))`, with
     `hw := conjugatesLevi_flattened_intersections ... hS hR`. So the factors of `X` are
     relabelled by the block bijection of `w` between the flattened refinements.

### Proof

1. *Extraction.* Let `J` be the normalized refined Jacquet module of the external tensor
   `externalSmoothObject Y` along `S`. It has finite length: the external tensor has finite
   length by the first lemma, and refined Jacquet functors preserve finite length
   (`Parabolic.normalizedRefinedFiniteLengthExactness`). The geometric piece applied to the
   external tensor is, definitionally, the refined induction along `R` of
   `(refinedIntersectionTransportFunctor ... hS hR).obj J`. This is used through
   `CuspidalSupport.geometricPieceSmoothFunctor_obj_toRep` and a `rfl` identification of
   `geometricPieceSmoothFunctor`. So `ρ` is a subquotient of `Φ.obj J`, where `Φ` is
   intersection transport, then normalized refined induction along `R`, then
   `restrictionFunctor (mulSingle j₀)`. Transport and normalized refined induction preserve
   finite length and short exact sequences of finite-length objects
   (`refinedIntersectionTransportFunctor_preservesFiniteLength/_preservesShortExact` and
   `normalizedRefinedFiniteLengthExactness`). The final restriction to the single block `j₀`
   preserves short exact sequences, since it keeps the underlying linear maps
   (`restrictionFunctor_preservesFiniteLengthShortExact`), but it need not preserve finite
   length: restricting to one factor of a Levi subgroup forgets the action of the other
   factors, and the result can have infinite length. Finite length of the restriction is not
   needed. `SmoothRep.PreservesFiniteLengthShortExact.comp` uses finite-length preservation
   only for the first functor of each composite, so `Φ` preserves short exact sequences of
   finite-length objects. Then `exists_irreducible_of_isSubquotient_map_of_finiteLength`
   (module `PieceTools`) applies. It needs only that `J` has finite length and that `Φ` sends
   the short exact sequences of a composition series of `J` to exact sequences. It gives an
   irreducible subquotient `τ` of `J` such that `ρ` is a subquotient of `Φ.obj τ`.
2. *Factorization.* Pull `τ` back to the flattened Levi `(B.flatten S).Levi` along
   `flattenedLeviEquivContinuous B S`. The pullback is irreducible
   (`isIrreducible_comp_continuousMulEquiv_iff`) and admissible
   (`CuspidalSupport.irreducibleLeviAdmissibility`). By
   `CuspidalSupport.padicLeviAdmissibleFactorization` it is equivalent to the block tensor of
   a family `X` of irreducible admissible representations. This is clause 1.
3. *Source.* Combining `SmoothRep.pullbackSymmIso`, the equivalence from step 2 and
   `Parabolic.flattenedTensorRefinedIso` shows that `τ` is isomorphic to the pullback, along
   the refined Levi equivalence, of the external tensor of the regrouped factors
   `flattenedBlockTensor T B S X`. These regrouped factors are irreducible
   (`flattenedBlockTensor_isIrreducible`). Since `τ` is a subquotient of the refined Jacquet
   module of the external tensor of `Y`, `Parabolic.subquotient_factor_of_refinedJacquet_external`
   gives clause 2.
4. *Target.* Let `σ` be the transport of `τ`. Combine
   `flattenedIntersectionTransportEquiv` (transport in flattened coordinates is the
   whole-Levi Weyl transport `CuspidalSupport.transport`), the equivalence from step 2 (via
   `FiniteTensorFiltration.compCongr`) and `transportExternalCastEquiv` (module
   `PieceTransport`). Together they identify the flattened pullback of `σ` with the external
   tensor of the cast family `X'`. As in step 3, `σ` is then isomorphic to the pullback of the
   external tensor of the regrouped family `flattenedBlockTensor T C R X'`.
   `refinedInductionObjEquiv`, `ProductLeviCuspidalJacquetAssembly.normalizedRefinedInducedCongr`
   and `Parabolic.refinedInductionTensor` show that the refined induction of `σ` is
   equivalent to the external tensor of the block inductions
   `T.normalizedParabolicInduced (R j) (flattenedBlockTensor T C R X' j).representation`. So
   `ρ` is a subquotient of the restriction of that external tensor along `mulSingle j₀`.
   Since `ρ` is irreducible, `isSubquotient_factor_of_external_comp_mulSingle` (module
   `PieceTools`) makes `ρ` a subquotient of the `j₀`-th factor. This is clause 3.

The proof sets `maxHeartbeats` to `1000000`, because the elaboration budget is counted for
the whole declaration.
