# Proof of commutativity for graded normalized GL induction over a local field

`Langlands.Aubert.LocalFieldGraded.localFieldGradedCommutativity` proves
`LocalFieldGradedCommutativityStatement` at independent universes `uF` and
`uV`. Its proof applies to every `AllFieldBZ.LocalFieldPackage`, of
characteristic zero or positive characteristic, and to every topological
datum. It also applies to every binary-product exact-length witness `h`. The
multiplication compared is the published `multiplication T h`, and both
variables range over the whole graded direct sum of exact Grothendieck
groups, including the rank-zero summand. Zelevinsky 1980, Theorem 1.9,
printed p. 174, is the source of the positive-rank argument. The rank-zero
summand is handled by a tensor-model comparison.

## Reduction to irreducible homogeneous classes

`multiplication_comm` compares the bilinear map `m = multiplication T h`
with its flip `m.flip`. `DirectSum.linearMap_ext` reduces the first variable
to a homogeneous summand of rank `a`. `Langlands.Aubert.hom_ext_irreducible`
then reduces it to the class of an actual irreducible smooth representation
`A` of `GL_a`. This lemma uses the bijective irreducible realization of the
exact finite-length Grothendieck group, so it accounts for all short exact
relations, including nonsplit ones. The same two reductions in the second
variable reach `irreducible_classes`: for irreducible `A` of rank `a` and
`B` of rank `b`, the products of their classes in the two orders agree.

`multiplication_homogeneous` and `binaryProduct_objects` rewrite each
product of homogeneous object classes as the inclusion, in total rank `a+b`
or `b+a`, of the class of the actual binary normalized product.
`inclusion_eq_of_reindexEquiv` compares two such inclusions: finite-length
representations of `GL_a` and `GL_b`, for `a = b`, have the same class in the
direct sum when the first is equivalent to the pullback of the second along
the entry-preserving reindexing `GeneralLinear.reindex (finCongr e)`.

## Positive ranks

Let `a, b > 0`. `sameFactors_binary` shows that the actual binary product of
`(A, B)` has the same Jordan–Hölder factors as the pullback of the product
of `(B, A)` along the reindexing for `a + b = b + a`.

- `binaryNormalizedProductPositiveIso` identifies each binary product with
  the block product along `BlockShape.binary`.
- `sameFactors_reverseProduct`, proved in
  `LocalFieldReversedProductConstituents`, matches the factors of the block
  product with those of the reversed block product.
- `reverse_binary` shows that the reverse of the binary shape `(a, b)` is the
  binary shape `(b, a)` cast to total rank `a+b`. `productObj_eq_of_shape`
  transports the factor family along this equality.
- `productRankCastEquiv` identifies the product along a rank-cast shape with
  the pullback of the uncast product along the reindexing.

The witness `h` gives both binary products finite length, and the reindexed
pullback keeps finite length by `pullbackFunctor_preservesFiniteLength`.
`ofRepresentation_eq_of_haveSameJordanHolderFactors` turns the matching
factors into equal exact classes. `inclusion_eq_of_reindexEquiv`, applied to
the identity equivalence, then removes the rank reindexing in the direct
sum. This is `positive_classes`.

## A rank-zero factor

`zeroLeftProductEquiv` compares the product of `(A, B)` with `A` of rank
zero and the product of `(B, A)`, pulled back along the reindexing for
`0 + b = b + 0`. It composes three equivalences:

1. the actual left-zero tensor model `binaryLeftZeroTensorEquiv`;
2. the tensor commutor `TensorProduct.comm`;
3. the inverse of the actual right-zero tensor model
   `binaryRightZeroTensorEquiv`, pulled back along the reindexing.

On pure tensors, the intertwining identity reduces to the composition rule
`reindex_trans` for entry-preserving reindexings. The rank-zero factor is an
arbitrary finite-length representation of the trivial group `GL_0`; it is
not replaced by the trivial line, so the case `a = b = 0` is included.
`zeroLeft_classes` deduces commutativity for arbitrary finite-length object
classes with first rank zero, and symmetry of equality gives the case where
the second rank is zero. The same tensor-commutor argument appears for
`p`-adic fields as `Langlands.Aubert.GradedCommutativityProof.zeroLeftProductEquiv`.

## Classification-module dependencies

The transitive dependencies of `localFieldGradedCommutativity` were computed
at Library commit `2f86a99eb5616254ac5b9c399603c9bbbea15f7a`, by the method
of the [GL rational comparison inventory](../../../notes/aubert/gl-rational-comparison-dependencies.md).
Starting from the theorem, every reached constant of a module under `Langlands`
was expanded through `Lean.ConstantInfo.getUsedConstantsAsSet` (type and
value). A classification-module constant is one whose defining module lies
under `Langlands.Representation.Classification` or
`Langlands.AllFieldBZ.Representation.Classification`, whatever its namespace.
The diagnostic compiled with no errors or warnings. The theorem depends only
on the axioms `propext`, `Classical.choice` and `Quot.sound`.

| Traversal root | Project constants | Project modules | Classification-module constants | Of these, theorems | Classification modules |
| --- | ---: | ---: | ---: | ---: | ---: |
| `localFieldGradedCommutativity` | 6,136 | 597 | 86 | 69 | 12 |
| `LocalFieldGradedCommutativityStatement` | 333 | 35 | 0 | 0 | 0 |

All 86 reached constants are listed below by defining module, each by its
full declaration name. Of these, 38 are compiler-generated auxiliaries
(`_proof_n` and `match_n` constants); the table names the declaration each
belongs to and gives their number.

| Defining module | Constants | Declarations reached |
| --- | ---: | --- |
| `Langlands.AllFieldBZ.Representation.Classification.CuspidalProductContragredient` | 1 | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.nonempty_contragredient_productEquiv` |
| `Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductEmbedding` | 4 | `Langlands.AllFieldBZ.Classification.irreducibleProductEmbedding`, `Langlands.AllFieldBZ.Classification.irreducibleProduct_embedding`, `Langlands.AllFieldBZ.Classification.irreducible_supercuspidalProduct_embedding`, `Langlands.AllFieldBZ.Classification.normalizedProduct_embedding_of_factor_embeddings` |
| `Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductEmbeddingStatement` | 1 | `Langlands.AllFieldBZ.Classification.IrreducibleProductEmbeddingTheorem` |
| `Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductFiniteLengthProof` | 3 | `Langlands.AllFieldBZ.Classification.irreducibleProductFiniteLength`; the private helpers with source names `Langlands.Classification.flattenSupercuspidalFactors` and `Langlands.Classification.flattenSupercuspidalFactors_obj` (declared as `_root_.Langlands.Classification` names in this module; their compiled names carry the module's private prefix) |
| `Langlands.AllFieldBZ.Representation.Classification.NormalizedProductFiniteLengthStatement` | 1 | `Langlands.AllFieldBZ.Classification.IrreducibleProductFiniteLength` |
| `Langlands.Representation.Classification.FiniteLengthProof` | 2 | `Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff`, `Langlands.FiniteLengthAssembly.length_comp_surjective` |
| `Langlands.Representation.Classification.IrreducibleProductEmbedding` | 1 | `Langlands.FiniteTensor.externalMap_injective` |
| `Langlands.Representation.Classification.Supercuspidal` | 11 | `Langlands.GeneralLinear.BlockShape.conjugateUnipotent`, `Langlands.GeneralLinear.IsSupercuspidal`, `Langlands.GeneralLinear.SupercuspidalRep`, `Langlands.GeneralLinear.isSupercuspidal_of_equiv`, `Langlands.GeneralLinear.supercuspidalProperty`, `Langlands.Jacquet.coinvariantsEquiv` (with 4 auxiliaries `_proof_1`–`_proof_4`), `Langlands.Jacquet.coinvariants_subsingleton_iff` |
| `Langlands.Representation.Classification.SupercuspidalContragredientAux` | 13 | `Langlands.GeneralLinear.isSupercuspidal_iff_standard`, `Langlands.Jacquet.coinvariantsConjEquiv` (with 6 auxiliaries `_proof_1`–`_proof_6`), `Langlands.Jacquet.coinvariants_conj_subsingleton_iff`, `Langlands.eq_zero_of_smoothDual_annihilates`, `Langlands.isIrreducible_iff_of_equiv`, `Langlands.isIrreducible_of_smoothContragredient`, `Langlands.isIrreducible_smoothContragredient_iff_of_bidual` |
| `Langlands.Representation.Classification.SupercuspidalSupport` | 5 | `Langlands.SmoothRep.IsSubquotient.of_iso_right`, `Langlands.SmoothRep.hom_hom_injective`, `Langlands.SmoothRep.hom_hom_surjective`, `Langlands.SmoothRep.isSubquotient_iff_exists` (with 1 auxiliary `Langlands.SmoothRep.isSubquotient_iff_exists.match_1_1`) |
| `Langlands.Representation.Classification.SupercuspidalTwist` | 1 | `Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup` |
| `Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof` | 43 | `Langlands.Classification.TwoFactorCommutativity.annihilator` (with 4 auxiliaries `_proof_1`–`_proof_4`), `Langlands.Classification.TwoFactorCommutativity.annihilatorQuotientEquiv`, `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict` (with 11 auxiliaries `_proof_1`–`_proof_11`), `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict_eq_zero_iff`, `Langlands.Classification.TwoFactorCommutativity.annihilatorRestrict_surjective`, `Langlands.Classification.TwoFactorCommutativity.annihilator_antitone`, `Langlands.Classification.TwoFactorCommutativity.annihilator_bot`, `Langlands.Classification.TwoFactorCommutativity.annihilator_top`, `Langlands.Classification.TwoFactorCommutativity.dualSeries` (with 4 auxiliaries `_proof_1`–`_proof_4`), `Langlands.Classification.TwoFactorCommutativity.dualSeries_graded`, `Langlands.Classification.TwoFactorCommutativity.haveSameJordanHolderFactors_of_comp`, `Langlands.Classification.TwoFactorCommutativity.isSmooth_quotientRep`, `Langlands.Classification.TwoFactorCommutativity.isSmooth_toRepresentation`, `Langlands.Classification.TwoFactorCommutativity.quotientProjection` (with 1 auxiliary `_proof_1`), `Langlands.Classification.TwoFactorCommutativity.quotientRepEquiv` (with 5 auxiliaries `_proof_1`–`_proof_5`), `Langlands.Classification.TwoFactorCommutativity.subrepInclusion` (with 2 auxiliaries `_proof_1`–`_proof_2`) |

An auxiliary listed as `_proof_k` after a declaration `D` is the compiled
constant `D._proof_k`.

The classification inputs therefore come from the all-field finite length and supercuspidal embedding of normalized products of
irreducibles, the smooth dual of a normalized product, supercuspidality and
contragredient helpers, and the dual-filtration and pullback-transport lemmas
of the two-factor constituent argument. No segment or Langlands-quotient
classification theorem is reached. The closure contains the all-field
`Langlands.LocalField.gelfandKazhdanContragredient`,
`Langlands.AllFieldBZ.Parabolic.productDualReversal`,
`Langlands.AllFieldBZ.Parabolic.nonempty_inverseTranspose_contragredient` and
`Langlands.AllFieldBZ.CuspidalSupport.cuspidalEmbedding`. It does not contain
the `p`-adic `Langlands.Classification.irreducibleProductFiniteLength` or
`Langlands.Classification.normalizedInductionFiniteLength`. The statement
alone reaches no classification module, so all 86 constants enter through
the proof.

- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  §1.9, printed p. 174.
