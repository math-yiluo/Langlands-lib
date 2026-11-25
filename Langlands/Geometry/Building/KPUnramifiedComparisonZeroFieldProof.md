# The depth-zero field for concrete unramified apartment lifts

`Langlands.Geometry.Building.unramifiedComparisonZeroField` proves exactly
`Langlands.Geometry.Building.UnramifiedComparisonZeroFieldStatement.{u}` at
arbitrary universe `u`, with the published hypotheses unchanged and no additional
premise. For every supplied lift `L` and downstairs apartment point `y`, it proves

```lean
((L.buildingData.moyPrasad L.centralizer_isTorus (L.e y) 0).comap
  (rationalExtend F (UnramifiedClosure F) G)).comap
    (rationalPoints.map P.centralizer.j) = P.centralizerZero
```

The upstairs subgroup is the actual norm-defined Moy–Prasad zero term. The two
preimages use the actual scalar-extension homomorphism and downstairs centralizer
inclusion. The theorem retains all original field, affine-group, building,
apartment-axiom, special-torus and lift quantifiers. It does not require a theorem
asserting that lifts exist.

## Implemented proof

For each lift, `UnramifiedZeroDatum.ofConnectedReductive` constructs a zero datum
`E` for the actual scalar-extended group, using
`L.buildingData.isConnectedReductive`. A private instance supplies the affine
structure morphism after base change by the same pullback argument as the target.

The proof then applies
`UnramifiedZeroDatum.zeroPoints_inf_fixer_eq_moyPrasad_of_sharpComparison` to
`E`, `L.buildingData`, the published unconditional theorem
`unramifiedZeroFixerSharpComparison`, `L.centralizer_isTorus`, and `L.e y`.
This identifies

```lean
E.zeroPoints ⊓ L.buildingData.fixer (L.buildingData.apartmentMap (L.e y))
```

with `L.buildingData.moyPrasad L.centralizer_isTorus (L.e y) 0`.
The imported comparison specializes the bounded sharp-fixer theorem to a
singleton. Its torus term is identified with the norm-Iwahori zero image by
`UnramifiedZeroDatum.wholeApartmentZeroFixer_eq_centralizerTorusImage`; the
remaining root term is the singleton sharp fixer, using
`pointwiseFixer_singleton` and `sharpFiltration_zero`.

Rewriting the target by this equality leaves exactly
`ApartmentLift.comap_zeroPoints_inf_fixer E y`, proved in
`KPUnramifiedComparisonZeroDescent`. That
imported descent theorem reflects fixation using the actual lift's restriction
identity, injectivity and normalizer compatibility. It combines character-kernel
descent and the norm-kernel consequence of centralizer fixation with
`ZeroSubgroupDatum.comap_unramifiedZeroPoints_inf_centralizerNormKernel` to
identify the double preimage with the unchanged `P.centralizerZero`.

The apartment-axiom hypothesis is introduced as part of the exact target and is
not needed in this assembly. Every mathematical comparison used here is supplied
by the named published Library results; no proposition target remains as a
premise.

## Provenance

This is a derived assembly of the published modules
`KPUnramifiedComparisonZeroDescent`, `UnramifiedMoyPrasadZeroFixerComparison`,
`KPZeroDatumExistence`, and `UnramifiedZeroFixerSharpComparisonProof`. The source
comparison with KP Definition 2.6.23(2), Corollary 9.7.3 and the first paragraph of
the proof of Lemma 9.8.1, including the 2024 corrections, is recorded in the
unchanged target Markdown `KPUnramifiedComparisonFieldStatements.md` and the
imported helper pairs. This module composes those results and does not change
the target or its imports.
