# Rational Kottwitz surjectivity from geometric inputs

This internal assembly completes the conditional proof route to `ChamberStatement`. It does not prove the unconditional target: all seven global inputs of `chamberStatement_of_remainingInputs` must still be supplied as theorems. Its provenance is composition of existing Library constructions and the preceding stable-chamber lifting and quotient assemblies. It introduces no independent assertion from the literature.

`RationalSurjectivityReductionStatement` asserts that the following six propositions imply surjectivity of the actual `reductiveKottwitzRational F G hG` for every nonarchimedean local field `F` and connected reductive group `G`:

- `SpecialTorusExistenceStatement`;
- `UnramifiedTwistedChamberStatement`;
- `UnramifiedParahoricModelStatement`;
- `IntegralModel.UnramifiedSmoothModelDescentStatement`;
- `UnramifiedChamberExactSequenceStatement`;
- `ReductiveKottwitzDescentStatement`.

There is no supplied building datum, chamber, or rational-surjectivity premise in this implication. The special torus and twisted-stable chamber propositions are explicit global assumptions, as are the model, exactness, and actual-map propositions. The conclusion uses the existing invariant target and the existing selected rational Kottwitz map.

The proof `rationalSurjectivityReduction` chooses a maximal split torus using the published `exists_maximalSplitTorus`, and applies the assumed special-torus proposition to place it in an `F`-defined closed subgroup that becomes maximal split over the actual maximal unramified extension `K`. The published `henselianDiscreteQuasiSplit` and `unramifiedQuasiSplit_of_henselianDiscrete` give quasi-splitness over `K`. The published `quasiSplitIntegerApartmentExistence` and `UnramifiedBuildingDescent.exists_omegaCompatible` then construct compatible apartment and centralizer data over `K`. Their class is Galois stable by the published `MaximalUnramified.galoisStable_of_isOmegaCompatible`.

The assumed twisted-chamber theorem, applied to the constant identity cocycle and the bottom finite intermediate field, supplies a chamber stable under the canonical coefficient action. The proof constructs its unramified zero datum with the published `UnramifiedZeroDatum.ofConnectedReductive`. Assumed chamber exactness supplies surjectivity and the neutral-kernel comparison upstairs. The preceding `stableChamberLifting` applies these facts, the two assumed model propositions, and the equivariance and restriction laws from the assumed actual-map descent proposition. This yields a lift in the rational setwise stabilizer of the chosen chamber. Forgetting stabilizer membership gives the claimed whole-group rational surjectivity.

Finally, `chamberStatement_of_remainingInputs` adds `ZeroKernelStatement` as its seventh explicit global input. It combines this surjectivity with `chamberStatement_of_surjective_of_geometricInputs`, whose quotient assembly proves normality of the intersection inside every supplied stable chamber's rational setwise stabilizer and the Kottwitz formula on every quotient representative. The result is exactly `ChamberStatement`, conditional on those seven global inputs. No input is discharged merely by this assembly.
