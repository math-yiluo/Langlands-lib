# The actual flattened and composed upper Jacquet quotients

`Langlands.Parabolic.FlattenedJacquetComparisonStatement.{uK,uF,uV}`
bundles two closed proposition definitions. This file supplies their
statements; it supplies no proof.

For every commutative ring `K` in `Type uK`, rank `n`, ordered block shape
`B` and ordered refinement `S` of `B`,
`FlattenedUnipotentComparisonStatement` asserts the literal subgroup
equality

```text
Parabolic.composedUnipotent K B S = (B.flatten S).unipotentSubgroup K.
```

Both sides are subgroups of the same actual matrix group
`GeneralLinear n K`. The left side is the inverse image of the inner upper
radical under the outer upper Levi projection (`leviPreimage` of
`refinedUnipotent`), as a subgroup of the ambient matrix group. The right
side is the standard upper radical of the ordered flattened shape, in the
given standard coordinates. There is no conjugation, free permutation or
supplied subgroup equality.

For a p-adic field `F` in `Type uF`, its topological datum `T`, and any
complex representation `ρ` of `GeneralLinear n F.Carrier` on a carrier `V`
in `Type uV`, put `C = B.flatten S` and
`e = Geometric.flattenedLeviEquiv F.Carrier B S`. The second clause,
`FlattenedNormalizedJacquetComparisonStatement`, asserts an actual
representation equivalence

```text
Representation.Equiv
  ((T.normalizedComposedJacquet B S ρ).comp e.toMonoidHom)
  (T.normalizedJacquet C ρ)
```

such that, for every original vector `v`,

```text
φ (Parabolic.composedJacquetMk B S ρ v) = C.jacquetMk ρ v.
```

The constructed group equivalence `e` goes from `C.Levi F.Carrier` to the
actual refined Levi subgroup `refinedLevi F.Carrier B S` of
`B.Levi F.Carrier`. Thus the source representation is pulled back along `e`
and has the same acting group as the standard flattened target. The
direction of the equivalence and its values on quotient representatives
are fixed. The statement requires invertibility and equivariance, beyond
existence of a linear surjection.

## Carriers and normalization

The source carrier `Parabolic.ComposedJacquetModule B S ρ` is the
coinvariant quotient of `V` by the ambient subgroup
`composedUnipotent F.Carrier B S`. Its action
`T.normalizedComposedJacquet B S ρ` twists the embedded block-diagonal
action by `Jacquet.inverseHalfCharacter (T.composedLeviModulus B S)`, the
inverse of the canonical positive half of the product of the outer and
inner full moduli.

The target carrier `C.JacquetModule ρ` is the published standard upper
Jacquet module: the coinvariants of the restriction of `ρ` to the actual
parabolic `C.parabolic F.Carrier` by its unipotent radical. It is a
different type from the ambient coinvariant quotient; the published
`BlockShape.jacquetModuleEquiv` relates the two. Its action
`T.normalizedJacquet C ρ` multiplies the embedded block-diagonal action by
`(T.leviHalfModulus C m)⁻¹`, the inverse half of the explicit full block
modulus `T.leviModulus C`.

Both sides therefore use inverse half-modulus normalization of their own
full modulus. No equality of moduli or of half characters is supplied as a
premise; a proof must derive it, for example from the published
`T.composedLeviModulus_flattened`, and must identify the ambient matrices,
for example by `Geometric.flattenedLeviEquiv_embedding`.

## Scope

The ring universe `uK`, p-adic-field universe `uF` and representation
carrier universe `uV` are independent. Both clauses include rank zero,
where the only shape has no blocks and the refinement family is empty,
families refining some or all blocks trivially, and zero representations. They assume no smoothness, admissibility, finite length,
irreducibility, positive rank, nonzero representation or nonempty
refinement.

This interface concerns the composed and flattened upper coinvariants. It
is distinct from the published opposite comparison
`FlattenedOppositeJacquetComparisonStatement`, from the upper
flattened-to-iterated surjection `FlattenedJacquetQuotientStatement`, and
from intrinsic natural transitivity of iterated and composed Jacquet
quotients. It asserts no tensor identification, occurrence, multiplicity,
finite-length or classification statement.

## Provenance

The exact interface is an internal finite-matrix and quotient-algebra
comparison derived from published Library definitions: the ordered matrix
constructions of `Geometric.FlattenedLevi`, the composed radical and
modulus of `Parabolic.RefinementComposition`, the composed normalized
quotient of `Parabolic.ComposedFunctors`, and the standard normalized
upper Jacquet module of `Jacquet.Parabolic`. It is not quoted from, or
attributed to, an external theorem. Its shape follows the published
opposite comparison `FlattenedOppositeJacquetComparisonStatement`, with the
upper radical, the standard parabolic-restriction carrier and the upper
normalized actions in place of the opposite ones. Existing Lean/Markdown
pairs are unchanged.
