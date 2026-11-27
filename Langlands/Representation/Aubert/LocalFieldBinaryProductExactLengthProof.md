# Proof of finite length and separate exactness of the local-field GL product

`Langlands.Aubert.localFieldBinaryProductExactLength` proves exactly
`Langlands.Aubert.LocalFieldBinaryProductExactLengthStatement.{uF,uV}`. It
keeps both universe parameters independent and adds no hypothesis. Given
`F : Type uF` with a field structure and any nonarchimedean local-field
realization `T : LocalFieldData F`, it forms the package
`K := AllFieldBZ.LocalFieldPackage.ofField F`. Then
`K.TopologicalData` is by definition `LocalFieldData K.Carrier`, so `T` is
used unchanged. For every pair of natural ranks `a, b` it proves the three
clauses for `binaryNormalizedProductFunctor.{uF, max uF uV} T a b`:
`PreservesFiniteLength₂`, `PreservesFiniteLengthShortExactLeft` and
`PreservesFiniteLengthShortExactRight`. The four private lemmas of the
module are stated for an arbitrary `K : AllFieldBZ.LocalFieldPackage.{uF}`
and an arbitrary carrier universe. The final theorem uses them at `ofField F`
and at the carrier universe `max uF uV` of the target.

## Positive ranks: separate exactness

`positiveProduct_exact` treats `a, b > 0` and
`binaryPositiveProductFunctor T ha hb`. By definition this functor is the pair
family `binaryPairFamilyFunctor T ha hb` followed by
`normalizedProductInductionFunctor` on the upper-block shape
`BlockShape.binary a b ha hb`. The latter is
`FiniteTensor.externalFunctor` followed by the normalized parabolic
induction functor of the same shape.

1. Let `Φ` be the pair family followed by `FiniteTensor.externalFunctor`. Its
   carrier is the indexed tensor product over `Fin 2` of the two input
   carriers. `BinaryProductExactness.pairSplit` identifies it with the
   ordinary tensor product of the two carriers. `BinaryProductExactness.pairSplit_map`
   says that the identification turns the mapped tensor into
   `TensorProduct.map` of the two input maps.
   `BinaryProductExactness.tensorModel_exact` then gives both
   `PreservesFiniteLengthShortExactLeft Φ` and
   `PreservesFiniteLengthShortExactRight Φ`. These statements come from
   exactness of the complex tensor product in each variable.
2. `Langlands.AllField.Parabolic.normalizedInductionExactness`, applied to the
   field `K.Carrier`, the realization `T` and the binary shape, turns every
   short exact sequence of smooth representations of the Levi subgroup into a
   short exact sequence of the induced maps. Its input is the three underlying
   representations, their smoothness proofs and the exactness data. No
   finite-length hypothesis is needed. Its three conclusions are injectivity,
   equality of range and kernel, and surjectivity. They are reordered to the
   order of `SmoothRep.IsShortExact`. The clause uses the half-modulus character
   `T.leviHalfCharacter` of the shape, which also defines the normalized
   parabolic induction functor. Its conclusion is therefore, by unfolding,
   the statement for the maps of
   `normalizedParabolicInductionFunctor T (BlockShape.binary a b ha hb)`.
3. Composing the two steps gives exactness in each argument for the positive
   product. Lean accepts the composite by unfolding the definitions above.

## Positive ranks: finite length

`positiveProduct_length` fixes finite-length `A` and `B` and uses
`Langlands.SmoothRep.preservesFiniteLength_of_irreducibles` twice. That theorem
says that a functor between smooth representation categories preserves finite
length if it maps finite-length short exact sequences to short exact sequences
and maps irreducible objects to finite-length objects.

1. First the right factor is fixed to the finite-length `B`. The functor is
   `Prod.sectL _ B ⋙ binaryPositiveProductFunctor T ha hb`, with variable left
   argument. Its exactness is the left clause of `positiveProduct_exact`, applied
   with the fixed finite-length factor `B`. The theorem reduces the claim to
   irreducible left factors `C`.
2. For an irreducible `C`, the left factor is then fixed to `C`. The functor is
   `Prod.sectR C _ ⋙ binaryPositiveProductFunctor T ha hb`, with variable right
   argument. Its exactness is the right clause of `positiveProduct_exact`,
   applied with the fixed factor `C`. `C` has finite length by
   `SmoothRep.hasFiniteLength_of_isIrreducible`. The theorem reduces the claim to
   irreducible right factors `D`.
3. For irreducible `C` and `D`, the product is the normalized product induction
   of the irreducible family `(binaryPairFamilyFunctor T ha hb).obj (C, D)` on
   the binary shape. Both blocks of the family are irreducible; the proof
   checks this by cases on `Fin 2`. Since `0 < a + b`,
   `Langlands.AllFieldBZ.Classification.irreducibleProductFiniteLength`, at the
   package `K`, the realization `T` and the shape `BlockShape.binary a b ha hb`,
   gives finite length of the product.

## All ranks

`binaryProduct_exact` splits on the ranks. If `a = 0`,
`binaryLeftZeroTensorEquiv` identifies the carrier of the product of
`X = (A, B)` with `A ⊗[ℂ] B`. Its naturality theorem
`binaryLeftZeroTensorEquiv_naturality` identifies the mapped vector with
`TensorProduct.map` of the two input maps. `tensorModel_exact` then gives both
clauses. This branch includes `a = b = 0`. If `a ≠ 0` and `b = 0`, the same
argument uses `binaryRightZeroTensorEquiv` and its naturality theorem. If both
ranks are positive, the proof rewrites with
`binaryNormalizedProductFunctor_of_pos` and applies `positiveProduct_exact`.

`binaryProduct_length` splits on the ranks in the same way. If `a = 0`, the
group `GeneralLinear a K.Carrier` is a subsingleton by
`GeneralLinear.subsingleton_of_rank_eq_zero`. It is therefore finite, so a
finite-length `A` is finite-dimensional over `ℂ` by
`finiteDimensional_of_isFiniteLength`. This result and the three below are in
the namespace `Langlands.Derivative.ProductDerivativesFiniteLength` of the
module `Langlands.Representation.Derivative.ProductDerivativesFiniteLength`.
The proof then uses, in order:

- `isFiniteLength_secondFactor`: `A ⊗[ℂ] B`, with `GL_b` acting on the second
  factor, has finite length.
- `isFiniteLength_comp`: finite length survives pullback along the surjective
  reindexing `GeneralLinear.reindex` from `GL_{a+b}` to `GL_b`. This pullback
  is the tensor model `rankZeroLeft`.
- `isFiniteLength_of_equiv`: finite length transfers along the inverse of
  `binaryLeftZeroTensorEquiv` to the product.

If `a ≠ 0` and `b = 0`, the argument is symmetric: `B` is finite-dimensional,
and the proof uses `isFiniteLength_firstFactor`, the tensor model
`rankZeroRight` and `binaryRightZeroTensorEquiv`. If both ranks are
positive, the proof rewrites with `binaryNormalizedProductFunctor_of_pos` and
applies `positiveProduct_length`.

## Use of the classification modules

The only classification result that the proof cites is
`Langlands.AllFieldBZ.Classification.irreducibleProductFiniteLength`. Its
statement is `Langlands.AllFieldBZ.Classification.IrreducibleProductFiniteLength`.
It is used only in the irreducible case of the positive-rank finite-length
argument. Exactness uses no classification result. Its proof proceeds as
follows:

1. `Langlands.AllFieldBZ.Classification.irreducibleProductEmbedding` embeds
   the product of the irreducible factors into the normalized product of
   blockwise products of supercuspidal representations.
2. `Langlands.AllFieldBZ.CuspidalSupport.glCuspidalTensor` shows that the
   external tensor product of the flattened supercuspidal family is
   irreducible and cuspidal for the Levi subgroup of the flattened shape.
3. `Langlands.AllFieldBZ.CuspidalSupport.cuspidalInductionLength` gives finite
   length of its induction.
4. `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` identifies this
   induction with the regrouped product.
5. Finite length then passes to the submodule given by the embedding.

The constants reachable from `localFieldBinaryProductExactLength` were
enumerated by a recursive traversal with `Lean.ConstantInfo.getUsedConstantsAsSet`,
which follows every constant used in the type or the value of each constant
reached; each reached constant was assigned to its defining module. The
traversal reaches 68,449 constants in the whole Lean environment, Mathlib and
the Lean core included. Of these, 5,237 are defined in 503 modules whose names
begin with `Langlands`, the proof module included, and 37 are defined in nine
modules whose names contain `Classification`. All 37 are reached through the
finite-length lemma `positiveProduct_length`; the same traversal from the
exactness lemmas `positiveProduct_exact` and `binaryProduct_exact` reaches none
of them. The nine modules are:

- `Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductFiniteLengthProof`
  holds `irreducibleProductFiniteLength` and two private helpers that
  flatten the supercuspidal factor family.
- `Langlands.AllFieldBZ.Representation.Classification.NormalizedProductFiniteLengthStatement`
  holds `IrreducibleProductFiniteLength`.
- `Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductEmbeddingStatement`
  holds `IrreducibleProductEmbeddingTheorem`.
- `Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductEmbedding`
  holds `irreducibleProductEmbedding`, `irreducibleProduct_embedding`,
  `irreducible_supercuspidalProduct_embedding` and
  `normalizedProduct_embedding_of_factor_embeddings`.
- Five modules under `Langlands.Representation.Classification` supply
  field-generic infrastructure: `Supercuspidal`,
  `SupercuspidalContragredientAux`, `SupercuspidalSupport`,
  `SupercuspidalTwist` and `IrreducibleProductEmbedding`. They provide the
  definitions `GeneralLinear.IsSupercuspidal` and `GeneralLinear.SupercuspidalRep`,
  the invariance of supercuspidality under equivalence, its test on the
  standard block unipotent radicals (`GeneralLinear.isSupercuspidal_iff_standard`)
  with the Jacquet coinvariant equivalences under equivalence and conjugation
  that these use, subquotient lemmas, the determinant of unipotent block
  elements and injectivity of external tensor maps.

None of the 503 `Langlands` modules that the traversal reaches has a name
containing `Segment`, `Multisegment`, `Zelevinsky`, `Tempered` or
`LanglandsQuotient`. In particular, the proof
uses neither the Zelevinsky segment and multisegment classification nor the
Langlands quotient classification.

## Provenance

The theorem is an internal consequence of results in the Library and adds no
external assertion. The paired statement Markdown cites Zelevinsky 1980
§§1.1, 1.4 and 1.7 for the target, and Bernstein–Zelevinsky 1977
§§1.8–1.9, 2.2–2.3, 2.5 and 2.8 for the tensor and induction exactness, the
irreducible embedding and the finite-length cuspidal-induction inputs. The
Lean proof combines the Library results for these inputs as described
above. It leaves the statement module and its imports unchanged.
