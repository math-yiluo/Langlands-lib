# One CM base field for all intermediate fields

Worker 84. The module
`Langlands/Global/Arithmetic/HenniartCommonBaseRealizationProof.lean` proves
`Langlands.Global.HenniartCommonBaseRealizationStatement.{uF}` as the theorem
`Langlands.Global.henniartCommonBaseRealization`. It adds no hypotheses or
axioms; the inspected axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Route

The proof reuses the construction behind the published
`Langlands.Global.harrisPairedPlaceRealization`. That proof globalizes a
finite Galois extension `Ω / ℚ_[p]` containing `F̃` by the CM rational Galois
model `N = cmModel p Ω`. It then takes the model fields of `F`, `F'` and `F̃`
in `N`. The model field of `F` is `E`. Its embedding into `F`,
`baseEmbedding p Ω N F.Carrier`, depends only on `Ω`, `N` and the
`F`-algebra structure of `Ω`, not on `F'`. In the published proof, however,
that `F`-algebra structure is built from `F̃ → Ω`, which changes with `F'`.

The module therefore proves three results.

1. `CMRealization.pairedPlaces_of_embeddings_spec` is the published
   `pairedPlaces_of_embeddings` with two further conclusions about the
   first place datum `P`. The prime `P.v` is the place cut out by `jE`
   (`b ∈ P.v` iff `‖jE b‖ < 1` for the spectral norm), and `P.iso` restricts
   to `jE` on `E`. Both facts come from `exists_harrisPlaceDatum`; the
   published proof discards the second one. The rest of the proof is the
   published one, unchanged.
2. `CMRealization.pairedPlaceConfiguration_of_model` is the published
   `pairedPlaceRealization_of_model` with `Algebra F.Carrier Ω` and
   `IsScalarTower F.Carrier F̃ Ω` given as hypotheses, and with
   `IsCMField E` an instance argument. The local tower instances are derived
   from these hypotheses instead of being defined as composites. The
   conclusion keeps `E` as the model field, states the paired-place
   configuration as `Harris.IsPairedPlaceConfiguration`, and adds the two
   facts from step 1.
3. `CMRealization.pairedPlaceConfiguration_of_le` applies step 2 to every `F'`
   with `F'.field ≤ M.field`. Here `Ω` contains the normal closure `M̃` of
   `M`, and `F̃' → Ω` is the inclusion `F̃' ≤ M̃`
   (`IntermediateField.normalClosure_mono`) followed by `M̃ → Ω`. The
   `F`-algebra structure of `Ω` is the one through `M̃` for every `F'`.

The theorem `henniartCommonBaseRealization` then:

- takes `Ω` from the published `exists_galois_extension` applied to `M̃`,
  fixes `Algebra F.Carrier Ω` through `M̃`, and takes `N = cmModel p Ω` with
  the published square roots, central automorphism and generation facts;
- proves `IsCMField E` by the published `isCMField_of_sq_neg`;
- applies step 3 with `F' = M` to get a place datum `P₀`, and sets
  `v₀ = P₀.v` and `ι₀ = P₀.iso`. Continuity of `ι₀` in both directions is
  part of the configuration;
- for each `F' ≤ M`, applies step 3 again. `P.v = v₀` because both primes
  have the same membership criterion through `jE`, and `P.iso` agrees with
  `ι₀` on `E` because both restrict to `jE`.

## Dependencies

Only published Library results and Mathlib are used: the CM model and
place-datum machinery of `CMPairedPlaceAssembly`, `CMPairedPlaceModel`,
`CMGaloisModel`, `GaloisModelRealization`, `HarrisPlaceFromEmbedding` and
`CMSubfield`, and `exists_galois_extension` from
`HarrisPairedPlaceRealizationProof`. The statement is in
`HenniartHarrisDatumStatement`.
