# Continuous representatives of compactly supported convolutions on the actual quotient

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeQuotientL2ContinuousRepresentativeStatement`
is a proposition definition. It supplies no proof.

## Setting

The objects are the Library's actual positive rational quotient
`PositiveRationalQuotient F G T i`, its canonical quotient Haar measure `μQ`
(`positiveRationalQuotientHaarMeasure`), its `L²` space and the integrated
original right action `haarQuotientL2IntegratedAction`, with the data and
hypotheses of `GroupSchemeQuotientL2Integrated`:

- `F` is a number field and `G` an affine group scheme over `Spec F`,
  locally of finite type.
- `T` is a commutative group scheme with a split-torus isomorphism `e`;
  `i : T.toGrp ⟶ G` is central with injective, finite-index character
  restriction.
- The Haar measure of the norm-one subgroup is right invariant.
- `μG` is the Haar measure of `G(A_F)`, and
  `positiveRationalSubgroupHaarMeasure` is the published measure on the
  subgroup `positiveRationalSubgroup` (positive real points of `T` times
  rational points) that is compatible with `μG` and `μQ`.

No compactness of the quotient, finite volume or connected reductivity is
assumed.

## Conclusion

For every compactly supported continuous `f` on `G(A_F)` and every class
`φ` in `L²(μQ)` there is a continuous function `ψ` on the quotient with
`R(f)φ = ψ` almost everywhere, and for every `x ∈ G(A_F)` and every uniform
bound `M` of `‖f‖`,
`‖ψ([x])‖² ≤ M · (∫ ‖f‖ dμG) · μ(H ∩ x S x⁻¹) · ‖φ‖²`, where
`S = supp f · (supp f)⁻¹`, `H` is the positive rational subgroup and `μ` its
published measure.

No smoothness, moderate growth, Hilbert–Schmidt or cuspidal conclusion is
asserted. The factor `μ(H ∩ x S x⁻¹)` is a count of rational points (times
a positive-torus volume) in a conjugated compact set; bounding it in `x` is
a separate task.

## Sources and provenance

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
registered as `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`: the
estimate (9.13) and point evaluations in Lemma 9.3.3, printed pp.247–248
(one-based PDF pp.259–260), and the first line of (9.14), printed p.250
(PDF p.262). This statement specializes
`Langlands.QuotientIntegration.QuotientIntegratedContinuousRepresentativeStatement`
to the actual quotient `[G] = A_G G(F) \ G(A_F)` with the split-centre
convention of Getz–Hahn (2.20), exactly as
`GroupSchemeCompactQuotientL2DecompositionStatement` specializes the
compact-quotient statements, but without compactness.

## Intended proof

A private proof compiles. It supplies the published instances and the
compatibility `positiveRationalQuotientHaarMeasure_isCompatible`,
identifies the original right action with coset right translation through
`coeFn_quotientL2RightTranslate`, and applies the left coset space
statement.
