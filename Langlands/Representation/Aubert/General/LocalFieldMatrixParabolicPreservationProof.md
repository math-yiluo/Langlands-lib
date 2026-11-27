# Proof of exactness and finite length for the matrix parabolic functors

`Langlands.Aubert.General.RationalPointFamily.GL.localFieldMatrixParabolicPreservation`
has type `LocalFieldMatrixParabolicPreservationStatement.{u,v}`. For each
`LocalFieldData F` and each rank and block shape, it proves both finite-length
preservation and preservation of short exact sequences of finite-length objects
at carrier universe `max (u + 1) v`. The functors are normalized induction with
the positive half-modulus and radical coinvariants twisted by its inverse.
[Statement](LocalFieldMatrixParabolicPreservationStatement.md)

In positive rank, `Langlands.AllField.CuspidalSupport.irreducibleLeviAdmissibility`
gives admissibility of the irreducible constituents of a finite-length Levi
representation. `SmoothRep.isAdmissible_of_finiteLength_of_irreducible` extends
admissibility along a composition series.
`Langlands.AllField.Classification.normalizedInductionFiniteLength` then gives
finite length of the induced representation. It uses exact induction and
finite length of induced products of irreducibles, which follows by embedding
the factors in supercuspidal inductions and regrouping.
[Product-Levi admissibility](LocalFieldProductLeviAdmissibility.md)

In rank zero, the conditions on block sizes force the block index set to be
empty. The Levi and ambient matrix groups are trivial. Evaluation at the
identity is an injective intertwiner because an induced function is determined
by its value at the unique group element. Its target is the inducing space
with the action pulled back along the surjective homomorphism of trivial
groups. This pullback preserves group-algebra length, and finite length passes
to the induced subrepresentation.

`Langlands.AllField.CuspidalSupport.cuspidalEmbedding` gives admissibility of
irreducible ambient representations. Extension along a composition series gives
admissibility of each finite-length ambient representation, which is also
finitely generated. `Langlands.AllField.Parabolic.normalizedJacquetFiniteLength`
applies to these two properties in every rank. Its proof uses admissibility and
finite generation of Jacquet modules and induction on `n - B.length` via proper
refinements.

The two short exactness clauses apply
`Langlands.AllField.Parabolic.normalizedInductionExactness` and
`Langlands.LocalFieldData.normalizedJacquetMap_exact` to the intertwiners underlying the
categorical maps. In each case the resulting injectivity, equality of image
and kernel, and surjectivity are the required conditions for the actual
functor maps.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The locators are VI.1.2, printed pp. 135–136, VI.6.2, p. 178, and VI.6.4,
p. 179. Renard uses the inverse convention for the parabolic modulus. His
normalized functors therefore have the half-power twists described above.

## Transitive classification dependencies

Starting from the theorem, the recursive closure of Lean declaration types and
values, including theorem bodies, reaches 67 constants in 13 classification
modules. The scan uses defining-module provenance for the
`Langlands.Representation.Classification`,
`Langlands.AllField.Representation.Classification`, and
`Langlands.AllFieldBZ.Representation.Classification` trees. The closure of the
statement alone contains zero such constants. The product-Levi admissibility
helper reaches the unipotent determinant identity in `SupercuspidalTwist`.
The constants reached by the full proof concern induction and Jacquet finite
length, supercuspidal embeddings, and their algebraic operations.

The inventory includes private and generated constants. Each group begins with
its defining module.

### `Langlands.AllField.Representation.Classification.FiniteLengthProof`

```text
Langlands.AllField.FiniteLengthAssembly.finiteLength_normalizedJacquet_of_refinements
Langlands.AllField.FiniteLengthAssembly.finiteLength_of_refinedJacquet
Langlands.AllField.FiniteLengthAssembly.isAdmissible_levi_subrepresentation
Langlands.AllField.FiniteLengthAssembly.isAdmissible_normalizedJacquet
Langlands.AllField.FiniteLengthAssembly.normalizedJacquet_eq_twist
Langlands.AllField.FiniteLengthAssembly.refinedJacquetMap_surjective
Langlands.AllField.FiniteLengthAssembly.refinement_measure_lt
Langlands.AllField.FiniteLengthAssembly.refinement_measure_lt._proof_1_1
Langlands.AllField.Parabolic.normalizedJacquetFiniteLength
```

### `Langlands.AllField.Representation.Classification.IrreducibleProductEmbedding`

```text
Langlands.AllField.Classification.irreducibleProductEmbedding
Langlands.AllField.Classification.irreducibleProduct_embedding
Langlands.AllField.Classification.irreducible_supercuspidalProduct_embedding
Langlands.AllField.Classification.normalizedProduct_embedding_of_factor_embeddings
```

### `Langlands.AllField.Representation.Classification.IrreducibleProductEmbeddingStatement`

```text
Langlands.AllField.Classification.IrreducibleProductEmbeddingTheorem
```

### `Langlands.AllField.Representation.Classification.IrreducibleProductFiniteLengthProof`

```text
Langlands.AllField.Classification.irreducibleProductFiniteLength
_private.Langlands.AllField.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.AllField.Classification.flattenSupercuspidalFactors
_private.Langlands.AllField.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.AllField.Classification.flattenSupercuspidalFactors_obj
```

### `Langlands.AllField.Representation.Classification.NormalizedProductFiniteLengthProof`

```text
Langlands.AllField.Classification.ProductLengthProof.irreducibleLevi
Langlands.AllField.Classification.ProductLengthProof.leviPreservation
Langlands.AllField.Classification.ProductLengthProof.step
Langlands.AllField.Classification.normalizedInductionFiniteLength
```

### `Langlands.AllField.Representation.Classification.NormalizedProductFiniteLengthStatement`

```text
Langlands.AllField.Classification.IrreducibleProductFiniteLength
```

### `Langlands.Representation.Classification.FiniteLengthProof`

```text
Langlands.FiniteLengthAssembly.complementaryProjection
Langlands.FiniteLengthAssembly.complementaryProjection._proof_1
Langlands.FiniteLengthAssembly.complementaryProjection._proof_2
Langlands.FiniteLengthAssembly.complementaryProjection_surjective
Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff
Langlands.FiniteLengthAssembly.finiteLength_of_complement
Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_2
Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_3
Langlands.FiniteLengthAssembly.finiteLength_of_injective
Langlands.FiniteLengthAssembly.finiteLength_of_surjective
Langlands.FiniteLengthAssembly.finite_of_surjective
Langlands.FiniteLengthAssembly.finite_summand
Langlands.FiniteLengthAssembly.length_comp_surjective
Langlands.FiniteLengthAssembly.length_eq_add_of_complement
```

### `Langlands.Representation.Classification.IrreducibleProductEmbedding`

```text
Langlands.FiniteTensor.externalMap_injective
```

### `Langlands.Representation.Classification.NormalizedProductFiniteLengthProof`

```text
Langlands.Classification.ProductLengthProof.finiteLength_of_injective
Langlands.Classification.ProductLengthProof.finiteLength_of_range_eq_ker
Langlands.Classification.ProductLengthProof.finiteLength_of_surjective
```

### `Langlands.Representation.Classification.Supercuspidal`

```text
Langlands.GeneralLinear.BlockShape.conjugateUnipotent
Langlands.GeneralLinear.IsSupercuspidal
Langlands.GeneralLinear.SupercuspidalRep
Langlands.GeneralLinear.isSupercuspidal_of_equiv
Langlands.GeneralLinear.supercuspidalProperty
Langlands.Jacquet.coinvariantsEquiv
Langlands.Jacquet.coinvariantsEquiv._proof_1
Langlands.Jacquet.coinvariantsEquiv._proof_2
Langlands.Jacquet.coinvariantsEquiv._proof_3
Langlands.Jacquet.coinvariantsEquiv._proof_4
Langlands.Jacquet.coinvariants_subsingleton_iff
```

### `Langlands.Representation.Classification.SupercuspidalContragredientAux`

```text
Langlands.GeneralLinear.isSupercuspidal_iff_standard
Langlands.Jacquet.coinvariantsConjEquiv
Langlands.Jacquet.coinvariantsConjEquiv._proof_1
Langlands.Jacquet.coinvariantsConjEquiv._proof_2
Langlands.Jacquet.coinvariantsConjEquiv._proof_3
Langlands.Jacquet.coinvariantsConjEquiv._proof_4
Langlands.Jacquet.coinvariantsConjEquiv._proof_5
Langlands.Jacquet.coinvariantsConjEquiv._proof_6
Langlands.Jacquet.coinvariants_conj_subsingleton_iff
Langlands.isIrreducible_iff_of_equiv
```

### `Langlands.Representation.Classification.SupercuspidalSupport`

```text
Langlands.SmoothRep.IsSubquotient.of_iso_right
Langlands.SmoothRep.hom_hom_injective
Langlands.SmoothRep.hom_hom_surjective
Langlands.SmoothRep.isSubquotient_iff_exists
Langlands.SmoothRep.isSubquotient_iff_exists.match_1_1
```

### `Langlands.Representation.Classification.SupercuspidalTwist`

```text
Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup
```
