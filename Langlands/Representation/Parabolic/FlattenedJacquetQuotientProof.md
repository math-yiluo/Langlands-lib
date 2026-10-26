# Equivariant surjectivity of the flattened Jacquet quotient

Author: Worker 434.

`Langlands.Parabolic.flattenedJacquetQuotient.{uF,uV}` proves the exact closed
`FlattenedJacquetQuotientStatement.{uF,uV}`. For every prime, p-adic field,
supplied topological data, block shape, ordered refinement and complex
representation, its witness is `flattenedJacquetQuotientMap`. The source is
the standard normalized Jacquet representation of the flattened shape. The
target is the iterated normalized Jacquet representation pulled back along
`Geometric.flattenedLeviEquiv`, from the flattened Levi to the actual refined
Levi subgroup of the outer Levi. The witness's underlying linear map is exactly
`CuspidalSupport.MinimalJacquet.flattenJacquetMap`.

The proof imports the full-character identity
`PadicField.TopologicalData.composedLeviModulus_flattened` from
`Parabolic.FlattenedRefinementModulusCalculation`. It reuses that determinant
calculation without reproving it or assuming any character comparison.
`flattenedLeviHalfModulus` applies the specified positive square-root unit map
and complex embedding to this full identity. The intrinsic
`composedLeviHalfModulus_eq` then yields, for
`e = flattenedLeviEquiv F.Carrier B S`,

```text
T.leviHalfModulus (B.flatten S) m =
  T.leviHalfModulus B (e m).val * T.refinedLeviHalfModulus B S (e m).
```

Taking inverses gives `flattenedLeviInverseHalfModulus`, the product identity
for the two Jacquet normalizing scalars. These identities use the actual
canonical positive halves; no square-root choice is introduced.

`flattenJacquetMap_mk` records that the fixed linear map sends the quotient
class of `v` to the inner quotient class of its outer quotient class.
`flattenJacquetMap_action_mk` expands the standard flattened action using
`normalizedJacquet_mk_eq_inv_halfModulus`. `normalizedIteratedJacquet_mk`
expands both stages using that formula and `normalizedRefinedJacquet_mk`.
Linearity moves the scalars through the quotient maps. The inverse-half
identity equates the resulting complex scalars, and
`flattenedLeviEquiv_embedding` identifies the ambient matrices acting on `v`.
This proves `flattenJacquetMap_equivariant_mk`. Surjectivity of the flattened
quotient map reduces every source vector to a representative, giving
`flattenJacquetMap_equivariant` and the intertwining field of the witness.
The existing `flattenJacquetMap_surjective` supplies its surjectivity; its
underlying linear-map equality is definitional.

The field and carrier universes remain independent. The proof includes rank
zero, empty block families, single-block refinements and zero representations.
It uses no smoothness, admissibility, finite-generation, finite-length,
irreducibility or nontriviality premise. Its conclusion is the prescribed
surjective intertwiner, without an injectivity or natural-isomorphism claim.

This is an internal derivation from published Library constructions: the
shared full-modulus calculation, canonical character operations, normalized
representative formulas, actual flattened Levi embedding compatibility, and
existing quotient map and surjectivity. No external source is attributed this
exact interface. The proof preserves its target and imported pairs and does
not use the consuming admissible finite-length theorem or downstream induction.
