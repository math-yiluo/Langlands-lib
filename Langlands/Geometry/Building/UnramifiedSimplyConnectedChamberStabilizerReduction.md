# Chamber stabilizers from the simply connected normalizer image

This internal reduction derives the original chamber-stabilizer target over
the maximal unramified extension from the full simply connected
normalizer-image assertion. The normalizer-image assertion remains an
explicit input; this module does not prove the unconditional target.
`UnramifiedSimplyConnectedChamberStabilizerProof` discharges that input with
the published normalizer theorem and proves the exact unconditional target.

## Arbitrary integer-valued building data

The two helpers in the namespace `IntegerValuationBuildingData` apply to any
field `k : Type u`, affine group scheme `G`, integer-valued valuation `v`,
and supplied `B : IntegerValuationBuildingData v G`. Such data already
include connected reductivity, maximal splitness and full omega
compatibility.

`normalizer_facet_fixing_of_range_le_affineWeylGroup` assumes

```text
B.apartment.normalizerAffineEquiv.range ≤
  AffineRootSystem.affineWeylGroup B.affineRoots.
```

It proves that each actual normalizer element preserving any full
apartment facet fixes that facet pointwise. The proof regards its original
affine action as an element of the affine Weyl subgroup and applies
`AffineRootSystem.affineWeyl_facet_fixing`. The locally finite reflection
arrangement needed there is supplied by
`isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs` and
`hasOppositeFactorPairs`, both for the same actual integer-valued data.
No order-one unit, positive-rank hypothesis or additional apartment axiom
is required.

`mem_pointwiseFixer_of_stabilizes_facet_of_range_le_affineWeylGroup`
retains the same containment premise. For every `B.IsFacet Y` and every
`g : rationalPoints G` preserving `Y` as a set, it proves
`g ∈ B.pointwiseFixer Y`.
The proof writes `Y` as a translated apartment facet and applies
`exists_normalizer_stabilizes_eq_on_translated_facet` from
`IntegerChamberStabilizerReduction`. This supplies a normalizer element
preserving the original facet and agreeing there with the conjugated
stabilizer action. The first helper fixes the facet pointwise. Substitution
in that agreement proves the original action fixes each point of `Y`,
which is exactly membership in the existing pointwise fixer.

## The exact target implication

`MaximalUnramified.SimplyConnectedChamberStabilizerReductionStatement.{u}`
is the Prop-valued implication

```text
MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u} →
  MaximalUnramified.SimplyConnectedChamberStabilizerStatement.{u}.
```

`MaximalUnramified.simplyConnectedChamberStabilizerReduction` proves that
implication. Given the normalizer-image statement, it introduces every
field, group, simple connectedness, building-datum, chamber and stabilizer
parameter of the unchanged target. A chamber is a full facet by its
apartment witness. The image equality supplied by the premise implies the
containment needed by the second helper, which then gives the target
pointwise-fixer membership. The universe remains arbitrary, the `K`-group
need not descend to the base local field, and the supplied building data
are unrestricted.

This is an internal composition of the named Library results and the two
separately stated propositions. It cites no additional external theorem.
The implication's input is
`MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement`. The final
proof module supplies it using the published unconditional theorem
`MaximalUnramified.simplyConnectedNormalizerAffineWeyl`.
