# Equivariant surjectivity of the flattened Jacquet quotient

Authors: Worker 322 and Worker 122 (target interface and scope).

`Langlands.Parabolic.FlattenedJacquetQuotientStatement.{uF,uV}` is a closed
Prop-valued definition. For every prime `p`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, rank `n`, block shape `B`, ordered refinement `S`,
and complex representation `ρ` on an arbitrary `V : Type uV`, it asserts
that the existing flattened-to-iterated quotient map is a surjective
intertwining map for the following actual representations.

Write `C = B.flatten S`, `e = Geometric.flattenedLeviEquiv F.Carrier B S`,
`J = T.normalizedJacquet B ρ`, and `K = T.normalizedRefinedJacquet B S J`.
The source representation is `T.normalizedJacquet C ρ` of `C.Levi F.Carrier`.
The target is `K.comp e.toMonoidHom`, a representation of the same group on
the iterated coinvariant carrier. Thus `m` acts in the target by `K (e m)`.
The equivalence `e` is the published coordinate construction into the actual
refined Levi subgroup of `B.Levi F.Carrier`, rather than additional input.

The existential witness `f` is required to satisfy both

```text
f.toLinearMap = CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ
Function.Surjective f.
```

Consequently its linear map is fixed: on representatives it sends

```text
C.jacquetMk ρ v  ↦  Geometric.refinedJacquetMk B S J (B.jacquetMk ρ v).
```

This formula follows from the existing definition of `flattenJacquetMap` as
`Jacquet.lift` of the composite quotient map. It is not a choice of a new
linear surjection. The `IntertwiningMap` type additionally requires, for every
`m : C.Levi F.Carrier` and source vector `x`,

```text
f ((T.normalizedJacquet C ρ) m x) = K (e m) (f x).
```

## Normalization and the remaining proof obligation

Both stages use the canonical inverse upper half modulus. On a representative,
the source action contributes `(T.leviHalfModulus C m : ℂ)⁻¹` and replaces
`v` by `ρ (C.leviEmbedding F.Carrier m) v`. The iterated target action
contributes the product of
`(T.leviHalfModulus B (e m).val : ℂ)⁻¹` and
`(T.refinedLeviInverseHalfModulus B S (e m) : ℂ)`.
The latter character is the inverse of the canonical positive refined half
modulus. The ambient embeddings agree by `Geometric.flattenedLeviEquiv_embedding`.

To establish equivariance on these representatives, the future proof must
compare the standard flattened half modulus with the product of the two
stage halves:

```text
T.leviHalfModulus C m =
  T.leviHalfModulus B (e m).val * T.refinedLeviHalfModulus B S (e m).
```

One route first proves the equality of positive full characters

```text
(T.composedLeviModulus B S).comp e.toMonoidHom = T.leviModulus C
```

and then applies the canonical positive square-root and inverse-half
constructions. The published `composedLeviHalfModulus_eq` and
`inverseHalf_composedLeviModulus` factor the intrinsically defined product
modulus; they do not by themselves identify it with the standard flattened
modulus. This comparison is a proof obligation, not a premise of the
proposition. The source is the actual standard flattened Jacquet action,
not the intrinsic `normalizedComposedJacquet` action.

The existing `flattenJacquetMap_surjective` already proves linear
surjectivity by lifting through both quotient maps. Linear surjectivity
alone gives no equality between normalized actions: the scalar factors
must also agree. Once that comparison is established, the published
`normalizedJacquet_mk_eq_inv_halfModulus`, `normalizedRefinedJacquet_mk`,
embedding identity and quotient surjectivity provide the representative
route to the intertwining equation. This paragraph describes a future
proof route; this module supplies only the proposition definition.

## Scope and provenance

The field and carrier universe levels are independent. Rank zero, its empty
block shape, single-block refinements and the zero representation are included.
There are no smoothness, admissibility, finite generation, irreducibility,
nontriviality or finite-length hypotheses, and no supplied modulus comparison.
The target asserts an equivariant surjection with its linear map prescribed;
it adds no injectivity, natural isomorphism or full transitivity assertion.

This is an internally derived statement about published Library constructions.
Its provenance is the actual coordinates and embedding law in
`Geometric.FlattenedLevi`, the quotient map and linear surjectivity in
`CuspidalSupport.MinimalJacquetProof`, the two normalized actions in
`Jacquet.Parabolic` and `Geometric.RefinementFunctors`, and the intrinsic
product-character identities in `Parabolic.RefinementComposition`.
No external source is claimed to state this exact Lean interface. The
module preserves those imported pairs and supplies no proof of the new
comparison. The proof must not depend on the consuming admissible
finite-length theorem or its downstream finite-type induction.
