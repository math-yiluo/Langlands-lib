# Proof of exactness and finite length inside a standard matrix Levi

`Langlands.Aubert.General.RationalPointFamily.GL.localFieldRefinedParabolicPreservation`
has type `LocalFieldRefinedParabolicPreservationStatement.{uF, uV}`, the
statement at its published universes. For every field `F` with
`LocalFieldData F`, every rank `n`, block shape `B` and block refinement `S`,
it proves the four clauses: normalized refined induction and normalized
refined Jacquet restriction both preserve finite length and short exact
sequences of finite-length objects, at carrier universe `max (uF + 1) uV`.
[Statement](LocalFieldRefinedParabolicPreservationStatement.md)

## Finite length of refined induction

Let `A` be a finite-length smooth representation of the refined Levi and
`ρ` its normalized refined induction to the outer Levi `B.Levi F`. Induce
`ρ` once more to `GL_n(F)`. Two comparisons identify this double induction
with a single normalized matrix induction:

- `iteratedInductionEquivComposed` is the equivalence from the iterated
  induction to the direct normalized composed induction. It is the component
  at `A` of the natural isomorphism supplied by
  `Langlands.AllField.Parabolic.normalizedRefinementInductionTransitivity`.
- `composedInductionEquivFlattened` gives an equivalence from the composed
  induction to normalized induction for the flattened block shape
  `B.flatten S`, applied to `A` pulled back along `flattenedLeviEquiv`. It
  specializes `Langlands.AllField.Parabolic.refinementCoordinatesNormalization`
  to the flattening equivalence of block coordinates.

The pullback along the group isomorphism has finite length
(`FiniteLengthAssembly.finiteLength_comp_surjective_iff`), so
`localFieldMatrixParabolicPreservation` for `B.flatten S` gives finite length
of the flattened induction, and the two injective equivalences carry it to the
double induction (`FiniteLengthAssembly.finiteLength_of_injective`). The same
theorem for `B` gives finite length of the ordinary normalized Jacquet module
of the double induction.

Evaluation at the identity,
`Langlands.AllFieldBZ.CuspidalSupport.jacquetEvaluation`, maps this Jacquet
module to `ρ`. It is surjective: for a vector `v`,
`Induction.compactLocalSection` gives a compactly supported induced section
whose value at the identity is `v`, and its class in the Jacquet module
evaluates to `v`. Being a quotient of a finite-length representation, `ρ` has
finite length (`FiniteLengthAssembly.finiteLength_of_surjective`).

## Finite length of refined Jacquet restriction

Let `A` be a finite-length smooth representation of the outer Levi and `X`
its normalized induction to `GL_n(F)`, which has finite length by
`localFieldMatrixParabolicPreservation` for `B`. The same theorem for
`B.flatten S` gives finite length of the normalized Jacquet module of `X` for
the flattened shape. `Langlands.AllField.Parabolic.flattenedJacquetQuotient`
gives a surjection from it onto the refined Jacquet module of the ordinary
Jacquet module of `X`, pulled back along `flattenedLeviEquiv`. That pullback
therefore has finite length (`FiniteLengthAssembly.finiteLength_of_surjective`),
and so does the iterated Jacquet module itself, by the reverse direction of
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` for the surjective
group isomorphism. Evaluation at the identity maps the ordinary
Jacquet module of `X` onto `A`, as above, and refined coinvariants preserve
surjections (`Langlands.coinvariants_map_surjective` through
`RefinedJacquetLengthProof.map_toLinearMap`). The refined Jacquet module of `A`
is therefore a quotient of a finite-length representation and has finite
length (`FiniteLengthAssembly.finiteLength_of_surjective`).

## Short exactness

For refined induction, injectivity and the equality of image and kernel hold
on function values (`Induction.smoothInducedMap_injective` and
`Induction.smoothInducedMap_range_eq_ker`). Surjectivity follows from
`Induction.smoothInductionSurjectivity`, whose hypotheses hold here: the
refined parabolic, a product of the standard parabolics of the factors, is
closed in the outer Levi; every neighbourhood of the identity in the outer
Levi contains a compact open subgroup
(`AllField.CuspidalSupport.levi_exists_compact_openSubgroup_subset`); and the
inflated, twisted inducing representations are smooth because the refined
half-modulus has open kernel
(`AllField.CuspidalSupport.isOpen_ker_refinedParabolicHalfModulus`).

For refined Jacquet restriction,
`AllField.CuspidalSupport.RefinedJacquetLengthProof.map_exact` gives
injectivity, exactness in the middle and surjectivity of the coinvariant maps
of the refined radical, which are the three required conditions.

No case distinction on the rank is needed; rank zero, with the empty block
shape and refinement, is covered by the same argument.

## Dependencies

Finite length of ordinary normalized matrix induction and of normalized
Jacquet modules comes from `localFieldMatrixParabolicPreservation`
([its proof](LocalFieldMatrixParabolicPreservationProof.md)). Finite length is
transferred under the Levi coordinate change and along intertwiners by
`FiniteLengthAssembly.finiteLength_comp_surjective_iff`,
`FiniteLengthAssembly.finiteLength_of_injective` and
`FiniteLengthAssembly.finiteLength_of_surjective` from
`Langlands.Representation.Classification.FiniteLengthProof`. The first
relates a representation to its pullback along `flattenedLeviEquiv`, in the
forward direction for refined induction and in the reverse direction for
refined Jacquet restriction; the second carries finite length through the two
comparison equivalences of refined induction; the third passes it to
quotients, namely to `ρ` from the Jacquet module of the double induction, to
the pulled-back iterated Jacquet module from the flattened one, and to the
refined Jacquet module of `A`. The remaining inputs are induction
transitivity, the coordinate comparison for flattened blocks, the flattened
Jacquet quotient, evaluation at the identity, and the exactness lemmas for
smooth induction and coinvariants.
