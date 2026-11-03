# Proper maps on actual points over locally compact fields: proofs

Authors: Worker 266 and Worker 712.

This module proves the published target
`Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointProperties`
(module `LocalFieldProperPointStatements`) with its exact hypotheses: `K` is an
arbitrary field in an arbitrary universe with a Hausdorff locally compact topology,
`IsTopologicalDivisionRing K`, and `hnondiscrete : ¬ DiscreteTopology K`. No norm,
valuation, characteristic restriction, projective embedding or Chow datum is used;
archimedean and nonarchimedean fields are treated uniformly. The point spaces are
the actual `RingPoint K X K` with `schemePointTopology`, and `f` is an actual
relative morphism; nonaffine and nonprojective schemes are included.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
Proposition 4.4, printed page 11 (registered source
`conrad-2011-weil-grothendieck-adelic-points`). Conrad treats projective maps and
then uses Chow's lemma and induction on dimension. The implemented proof takes a
different route: ultrafilter limits, an ultrapower of `K`, and the valuative
criterion for universally closed morphisms in Mathlib.

## `schemePointLocalProperness_proof`

Statement: `SchemePointLocalPropernessProperty K hnondiscrete`.

Proof as implemented. Fix `X`, `Y` and `f` with `IsProper f.left`. By
`isProperMap_iff_ultrafilter` it suffices to show continuity, which is the
Library's `schemePointContinuity_proof K K X Y f`, and that for every ultrafilter
`𝒰` on `RingPoint K X K` and point `y` with `p ≫ f → y` along `𝒰` there is `x`
with `x ≫ f = y` and `𝒰 ≤ 𝓝 x`. This is `exists_limit_of_valuationSubring`
(module `LocalFieldProperPointLimits`) applied to the identity family, with
`L = UltrapowerField K 𝒰`, `G = ultrapowerMap K 𝒰`, `O = convergentGerms K 𝒰
hnondiscrete` and `ρ = standardPart K 𝒰 hnondiscrete` from the module
`LocalFieldUltrapower`. Its hypotheses are: germs of eventually equal functions
are equal (`Germ.coe_eq`, after `ultrapowerMap_apply`); the germ of a convergent family lies in `O`
(`mem_convergentGerms_iff`); and a family whose germ is `a ∈ O` converges to
`ρ a` (`tendsto_standardPart`). The properness hypothesis enters through
`QuasiCompact f.left` and `UniversallyClosed f.left`, consequences of
`IsProper f.left`.

## `localFieldProperPointProperties_proof`

Statement: `LocalFieldProperPointProperties K hnondiscrete`, exactly the target.

Proof: the first clause is `schemePointLocalProperness_proof`; the second
follows from it by `properSchemeLocalPointCompactness_of_properness`
(module `LocalFieldProperCompactnessReduction`), which applies the first clause
to the structure morphism of a proper scheme, viewed as a morphism to
`Over.mk (𝟙 (Spec K))`, whose actual point space is a subsingleton, and takes
the compact preimage of the whole space.

## Helper modules

- `LocalFieldInverseBound`: a compact set containing every element or its inverse.
- `LocalFieldUltrapower`: the ultrapower field, its valuation subring of
  convergent germs and the limit map (`standardPart`).
- `LocalFieldProperCompactnessReduction`: the compactness clause from the
  properness clause.
- `LocalFieldProperPointCharts`: chart, basic-open and germ-transfer lemmas.
- `LocalFieldProperPointLimits`: the abstract limit theorem via the valuative
  criterion.
