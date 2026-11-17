# The Galois-stable Iwahori chamber over the maximal unramified extension

`Langlands.GroupScheme.localSimplyConnectedUnramifiedChamber` proves exactly
`LocalSimplyConnectedUnramifiedChamberStatement.{u}`, at arbitrary universe `u` and with no
additional premises.

Let `F` be a nonarchimedean local field and `L = inertiaFixedField F`. Let `G` be an affine,
simply connected group over `F`. The statement then supplies the following data:

- building data `C` for `G_L`, with a semilinear Galois action `D`;
- a smooth integral model `M` of `G` over `𝒪[F]` whose special fibre over `𝓀[F]` is connected;
- a chamber `Y₀` of the reduced building of `G_L`.

These satisfy four conditions. `Y₀` is stable under every `D.action σ`. The image of
`M(𝒪_L)` in `G(L)` is the setwise stabilizer of `Y₀`. `G(L)` acts transitively on the
chambers. Finally, for every crossed homomorphism `c` that is trivial on the fixing subgroup
of a finite subextension, some chamber is stable under `y ↦ c(σ) · D.action σ y`.

## The proof

The proof is a single term. It applies the published conditional assembly
`localSimplyConnectedUnramifiedChamberAssembly`
(`LocalSimplyConnectedUnramifiedChamberAssemblyStatement`) to published unconditional proofs
of its five premises:

1. `UnramifiedQuasiSplitStatement` is
   `unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit`. This is the
   published reduction applied to the published Henselian discretely valued
   quasi-splitness theorem.
2. `SpecialTorusExistenceStatement` is `Langlands.Geometry.Building.specialTorusExistence`.
3. `MaximalUnramifiedAffineWeylStatement` is
   `Langlands.Geometry.Building.maximalUnramifiedAffineWeyl`.
4. `UnramifiedTwistedChamberStatement` comes from four published results, composed as
   follows:
   - `unramifiedTwistedChamberQuotient` proves `UnramifiedTwistedChamberQuotientStatement`.
   - `unramifiedTwistedGeneratorChamber_of_quotient` turns it into
     `UnramifiedTwistedGeneratorChamberStatement`.
   - `unramifiedTwistedChamberThroughFixedPointReduction` then gives
     `UnramifiedTwistedChamberThroughFixedPointStatement`.
   - `unramifiedTwistedChamber_of_metric` combines that with `unramifiedBuildingMetric`, a
     proof of `UnramifiedBuildingMetricStatement`.
5. `LocalSimplyConnectedUnramifiedIwahoriModelStatement` is
   `Langlands.GroupScheme.localSimplyConnectedUnramifiedIwahoriModel`.

The assembly constructs `C` and `D` from a special maximal torus and an `ω`-compatible
apartment. The trivial twist (`c = 1`, `E = ⊥`) in input 4 gives a Galois-stable chamber
`Y₀`. Input 5 gives the smooth model with connected special fibre and the
stabilizer identity. Input 3 and affine chamber simple transitivity give transitivity
on chambers. Input 4 gives the twisted chamber for every admissible `c`.

## Import compatibility edit

The proof imports both `UnramifiedTwistedChamberQuotientProof` and
`UnramifiedBuildingMetricProof`/`SpecialTorusExistenceProof`. Their import closures contain
`IntegerBuildingFacetCentroids` and `IntegerValuationBuildingMetricReduction`, respectively.
Both modules declared anonymous local instances of `NormedAddCommGroup`, `NormedSpace ℝ`
(and `FiniteDimensional ℝ`) on `TranslationSpace B.i` in the namespace
`IntegerValuationBuildingData`. The generated names coincided, so no module could import
both. This candidate therefore names the three local instances of
`IntegerBuildingFacetCentroids` explicitly: `centroidNormedAddCommGroup`,
`centroidNormedSpace` and `centroidFiniteDimensional`. Their types and values are unchanged,
and they remain `local`. That module's Markdown records this. No statement changes, and
neither module is in the import closure of the target statement.

## Provenance

This is an internal composition of published Library results. The comparison of the
target with Kaletha–Prasad, Theorem 10.6.1 and its proof is in the unchanged
[statement Markdown](LocalUnramifiedChamberStatement.md). The comparison of the five
inputs is in the Markdown of the [assembly](LocalUnramifiedChamberAssembly.md) and of
each input statement.
