# Actual flattened tensor Jacquet occurrences

Author: Worker 19.

This internal adapter relates actual standard flattened Jacquet occurrences
to actual composed and blockwise occurrences. It retains every coarse block
and the exact rank transport of every original factor, the supplied
topology, and independent field and carrier universes. It proves no local
binary or rank-three transfer.

`SmoothRep.pullbackSymmIso` cancels inverse common group pullbacks using
the identity linear map. `subquotient_pullback_right_iff` applies this to
move a group equivalence from the ambient to the constituent of an actual
subquotient.

`flattenedBlockFactor` transports each original factor along the proved
flattened-size equality. `flattenedBlockTensor` tensors that entire
inner-block family. `flattenedTensorRefinedIso` bundles the existing
rank-aware tensor regrouping equivalence over the actual refined subgroup.
`flattenedComposedJacquetIso` bundles the actual normalized quotient
comparison over the standard flattened Levi.
`subquotient_flattenedJacquet_iff` combines this comparison with inverse
group pullback cancellation.

`flattenedBlockTensor_isIrreducible` requires every original factor to be
irreducible and admissible. Each exactly rank-transported factor retains
both properties by equality elimination. Admissible Schur makes every
self-intertwiner a scalar; the existing finite tensor irreducibility
theorem applies to each entire inner tensor.

For positive total rank, `exists_factorized_coarseJacquet_of_flattened`
takes an admissible finite-length smooth ambient representation `π`, an
arbitrary ordered refinement `S` of a coarse shape `B`, a family `C` of
admissible irreducible factors on `B.flatten S`, and the actual occurrence
of their entire external tensor in the standard upper normalized Jacquet
module of `π`. It returns a family `A` on all coarse blocks such that:

- Every `A i` is irreducible, admissible and of finite composition length.
- The whole external tensor of `A` is an actual subquotient of the coarse
  normalized Jacquet module of `π`.
- For every coarse block `i`, the actual tensor `flattenedBlockTensor ... C i`
  is an actual subquotient of the normalized Jacquet module of `A i` at
  the inner shape `S i`.

The implementation proves irreducibility of the original entire tensor
using admissible Schur and the existing finite tensor theorem. Pullback
along the inverse continuous flattened Levi equivalence preserves that
irreducibility. The actual flattened/composed occurrence equivalence then
supplies the hypothesis of
`exists_factorized_coarseJacquet_subquotient`. The extracted coarse tensor
retains the actual refined occurrence. Transport its constituent through
`flattenedTensorRefinedIso`, prove each nested tensor irreducible, and apply
`subquotient_factor_of_refinedJacquet_external` to extract the stated
blockwise occurrences.

`subquotient_flattenedJacquet_of_coarse_factors` takes only the actual coarse
occurrence of the external tensor of `A` and the actual blockwise
occurrences of the regrouped `C` tensors in its block Jacquets. The
factorwise refined return theorem reassembles them. Transport the
constituent through the inverse regrouping isomorphism, use actual
Jacquet exactness and transitivity to return to the composed Jacquet module
of `π`, and apply the flattened/composed occurrence equivalence in reverse.
This direction requires no irreducibility, admissibility, finite length,
positivity of total rank, or dimension hypothesis. Both directions retain
every original factor and every coarse block. The ambient `π` need not
be irreducible, and no whole-Jacquet quotient or induction embedding is
assumed.

All factor carriers remain in `Type uV`, independently of the field
universe `uF`. The host task uses the specialization of this carrier
universe to `max uF uV`. The topology is exactly the supplied `T.topology`;
its ring continuity is derived from `T.valuativeRel` and `T.localField`.
There is no cuspidal-line, linkage, distinctness or support restriction
on outside factors.

## Dependency audit

The provenance is internal. The five direct imports are
`Filtration.CoarseJacquetFactorization`, `Parabolic.RefinedTensorOccurrences`,
`Parabolic.FlattenedJacquetComparisonProof`,
`Tensor.FlattenedGLRefinement`, and `Tensor.FiniteProperties`. Recursive
traversal over Library base `125fca1a70e8f89af98a36c8565617cd68f73be5`
contains 379 project modules, including this one and the separately staged
prerequisites. The classification-named modules are exactly
`CanonicalConstituents`, `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`, `Essential`, `FiniteLengthProof`,
`FiniteLengthStatement`, `RelativeGenericityStatement`,
`RelativeJacquetMultiplicityStatement`, `RelativeRegularComparisonStatement`,
`Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalSupport`,
`SupercuspidalTwist`, `Tempered`, `TemperedInductionStatement`, and
`TemperedSupportStatement`.

The used proof routes were checked at declaration level:

- `FlattenedJacquetComparisonProof` proves equality of the actual composed
  upper radical and the standard flattened radical by checking their
  matrix entries. Its comparison changes only the relation-subgroup
  equality and the existing actual Jacquet carrier identification.
  The forward comparison sends every original vector's quotient class
  to its quotient class. Equivariance uses the equality of the actual
  ambient block embeddings and the inverse positive half of the full
  modulus.
- `FlattenedRefinementModulusCalculation` proves the required full-modulus
  equality by computing block-diagonal determinants and separating the
  flattened lexicographic determinant product into pairs in different
  outer blocks and pairs in the same block. The rectangular product
  identity and each inner shape's rank sum give the composed product.
  Applying the positive square-root character gives the half-modulus
  comparison. No analytic continuation or classification assertion
  enters this calculation.
- `Tensor.GLRefinement` regroups the actual original tensor by its finite
  dependent block partition and applies the linear carrier transports
  for the proved rank equalities. Pure-tensor formulas verify
  equivariance for the actual matrix-reindexing group map.
  `Tensor.FiniteRegrouping` constructs the dependent tensor associator
  by finite outer induction, with the empty tensor and head/tail tensor
  equivalences. The flattened specialization identifies exactly the
  same group map as `flattenedLeviEquiv`.
- `admissibleSchur_scalarEndomorphism` restricts an endomorphism to a
  finite-dimensional nonzero space fixed by an open subgroup, chooses a
  complex eigenvector, and uses irreducibility to make the resulting
  scalar operator identity global. `FiniteTensor.isIrreducible_external`
  applies Jacobson density to finite coefficient supports in a tensor
  basis. From any nonzero invariant vector it obtains all pure tensors;
  the tensor basis also proves nonzeroness. The short private wrapper
  repeats the same specialization as
  `Parabolic.WholeLeviConjugacyProof.isIrreducible_external_of_admissible`,
  avoiding that module's additional induction and association
  infrastructure.
- The whole-coarse extraction uses actual finite image filtrations and a
  composition series, actual refined coinvariant exactness by smooth
  averaging, and normalized quotient transitivity. Coarse Jacquet finite
  length is the lower rank-induction proof using compact-coefficient
  quasicuspidal splitting and detection by proper refinements.
  Admissibility of an actual subquotient follows from compact open
  averaging and the presenting kernel sequence. Coarse factorization
  uses compact averaging and a minimum fixed-space dimension to obtain
  a simple first factor, then admissible Schur, Jacobson density and
  actual multiplicity-space evaluation. The detailed bodies are also
  described in `CoarseJacquetExtraction.md` and
  `CoarseJacquetFactorization.md`.
- `RefinedTensorOccurrences` supplies the upper normalized actual
  product-subgroup quotient comparison and the actual tensor occurrence
  extraction and return. Its maps descend tensor quotient projections
  and their inverse through the actual relation submodules. Smooth
  actual-subquotient presentations, common group pullbacks and linear
  tensor splittings are detailed in its paired Markdown and
  `Tensor/SmoothSubquotients.md`.

The classification-named imports supply lower definitions, statement
interfaces and the independent finite-length proof just described. The
used bodies invoke no global support decomposition, general ordered
quotient coverage, full multisegment classification or any conclusion of
the eight classification tasks excluded by the host contract, including
their proof successors. Neither local binary identification nor local
rank-three structure is asserted here. Applying this bridge to the host's
literal original and permuted shapes still requires the corresponding
block combinatorics and local transfer proofs.
