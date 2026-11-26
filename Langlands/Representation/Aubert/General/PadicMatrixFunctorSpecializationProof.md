# The p-adic specialization of the local-field matrix functors: proof

`Langlands.Aubert.General.RationalPointFamily.GL.padicMatrixFunctorSpecialization`
proves `PadicMatrixFunctorSpecializationStatement.{u, v}` at independent
universe levels `u` (the field) and `v` (the representations), with no
further hypothesis. The argument is uniform in the prime `p`, the p-adic
field `F`, its topological data `T`, the rank `n` (rank zero included) and the
ordered block shape `B`.

## Equality of the functors

`PadicField.TopologicalData.toLocalFieldData` (in `Langlands.LocalField.PadicBridge`)
builds the `LocalFieldData` of `F.Carrier` from the topology, valuation and
local-field structure of `T` and nothing else. Both normalized induction
functors are `BlockShape.normalizedInductionFunctorOf` applied to the half
character `leviHalfCharacter B` of their data. Both normalized Jacquet functors
are `BlockShape.normalizedJacquetFunctorOf` applied to `leviModulus B` and the
openness of its kernel. In both settings `leviModulus B` is the same product of
powers of the block determinant norms. The determinant norm of
`T.toLocalFieldData` is the one of `T`, because its residue cardinality and
normalized absolute value are those of `T` by definition (see
`toLocalFieldData_residueCardinality` and `toLocalFieldData_normalizedAbs`).
So the two functors agree on objects and maps by definitional unfolding, and
both equalities of bundled functors on the full smooth categories are proved by
`rfl`.

## Finite length and exactness

Because the local-field functors are definitionally the p-adic functors, the
p-adic results apply to them directly, at the carrier universe
`max (u + 1) v`:

- `Langlands.Parabolic.normalizedParabolicFiniteLength.{u, max (u + 1) v} F T`
  gives `PreservesFiniteLength` for both functors (its first and second
  components at `n` and `B`).
- `Langlands.Parabolic.FiniteLengthGrothendieckAssembly.normalizedInductionFunctor_preservesShortExact F T B`
  and `normalizedJacquetFunctor_preservesShortExact F T B` in the same namespace
  give `PreservesFiniteLengthShortExact` for induction and Jacquet restriction.

## The Grothendieck maps

`Parabolic.normalizedInductionK0 F T B` is `B.finiteLengthMapToGeneralLinear`
of the p-adic induction functor with the two preservation proofs above, and
`Parabolic.normalizedJacquetK0 F T B` is `B.finiteLengthMapFromGeneralLinear`
of the p-adic Jacquet functor with its two proofs. Both unfold to
`SmoothRep.FiniteLengthGrothendieckGroup.map`. The preservation hypotheses are
propositions, so any supplied witnesses `hi`, `hix`, `hr`, `hrx` are
definitionally equal to the published ones by proof irrelevance. Each equality
of maps is therefore proved by `rfl`, for every choice of the witnesses.

## Transitive dependencies

The type and value of the theorem were traversed in the Library's Lean
environment at Library commit `66a181ec9cda271c1ff0dcf555f386b52dc687c7`. The
traversal expands every reached constant of the Library (modules under
`Langlands`, `Nyll`, `StacksCore`, `StacksFrontier` and `FontaineWintenberger`)
with `Lean.ConstantInfo.getUsedConstantsAsSet`, and assigns each constant to its
defining module; constants of Lean, Mathlib and other packages are not
expanded. Every reached Library constant is defined in a module under
`Langlands`. A classification constant is one defined in a module with a
`Classification` component.

| Root | Library constants | Defining modules | Classification constants | Of these, theorems | Classification modules |
| --- | ---: | ---: | ---: | ---: | ---: |
| `padicMatrixFunctorSpecialization` | 5,489 | 469 | 67 | 56 | 10 |
| `PadicMatrixFunctorSpecializationStatement` | 5,488 | 468 | 67 | 56 | 10 |

The statement alone already reaches all 67 classification constants: the
definitions of `Parabolic.normalizedInductionK0` and
`Parabolic.normalizedJacquetK0` contain the finite-length proofs. The proof
adds only the theorem itself. All ten classification modules lie under
`Langlands.Representation.Classification`. The reached declarations are the
following.

- `FiniteLengthProof`: `Langlands.Parabolic.normalizedJacquetFiniteLength` and
  22 constants of `Langlands.FiniteLengthAssembly` (`complementaryProjection`
  with its two generated proofs, `complementaryProjection_surjective`,
  `finiteLength_comp_surjective_iff`,
  `finiteLength_normalizedJacquet_of_refinements`, `finiteLength_of_complement`
  with two generated simp lemmas, `finiteLength_of_injective`,
  `finiteLength_of_refinedJacquet`, `finiteLength_of_surjective`,
  `finite_of_surjective`, `finite_summand`,
  `isAdmissible_levi_subrepresentation`, `isAdmissible_normalizedJacquet`,
  `length_comp_surjective`, `length_eq_add_of_complement`,
  `normalizedJacquet_eq_twist`, `refinedJacquetMap_surjective`,
  `refinement_measure_lt` and its generated proof).
- `IrreducibleProductEmbedding`:
  `Langlands.Classification.irreducibleProductEmbedding`,
  `irreducibleProduct_embedding`, `irreducible_supercuspidalProduct_embedding`,
  `normalizedProduct_embedding_of_factor_embeddings` and
  `Langlands.FiniteTensor.externalMap_injective`.
- `IrreducibleProductEmbeddingStatement`:
  `Langlands.Classification.IrreducibleProductEmbeddingTheorem`.
- `IrreducibleProductFiniteLengthProof`:
  `Langlands.Classification.irreducibleProductFiniteLength` and the private
  `flattenSupercuspidalFactors` with its lemma `flattenSupercuspidalFactors_obj`.
- `NormalizedProductFiniteLengthProof`:
  `Langlands.Classification.normalizedInductionFiniteLength` and six constants of
  `Langlands.Classification.ProductLengthProof` (`finiteLength_of_injective`,
  `finiteLength_of_range_eq_ker`, `finiteLength_of_surjective`,
  `irreducibleLevi`, `leviPreservation`, `step`).
- `NormalizedProductFiniteLengthStatement`:
  `Langlands.Classification.IrreducibleProductFiniteLength`.
- `Supercuspidal`: `Langlands.GeneralLinear.BlockShape.conjugateUnipotent`,
  `Langlands.GeneralLinear.IsSupercuspidal`, `SupercuspidalRep`,
  `isSupercuspidal_of_equiv`, `supercuspidalProperty`, and
  `Langlands.Jacquet.coinvariantsEquiv` with its four generated proofs and
  `coinvariants_subsingleton_iff`.
- `SupercuspidalContragredientAux`:
  `Langlands.GeneralLinear.isSupercuspidal_iff_standard`,
  `Langlands.Jacquet.coinvariantsConjEquiv` with its six generated proofs,
  `coinvariants_conj_subsingleton_iff` and
  `Langlands.isIrreducible_iff_of_equiv`.
- `SupercuspidalSupport`: `Langlands.SmoothRep.IsSubquotient.of_iso_right`,
  `hom_hom_injective`, `hom_hom_surjective`, `isSubquotient_iff_exists` and its
  generated matcher.
- `SupercuspidalTwist`:
  `Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup`.

These come from the p-adic finite-length theorems for the matrix functors:
finite length of normalized induction
(`Langlands.Classification.normalizedInductionFiniteLength`), of Jacquet
restriction (`Langlands.Parabolic.normalizedJacquetFiniteLength`), and of
products of irreducible representations through their supercuspidal
embeddings (`Langlands.Classification.irreducibleProductEmbedding`,
`Langlands.Classification.irreducibleProductFiniteLength`). No
segment-classification theorem and no Langlands-quotient classification
theorem is reached.
