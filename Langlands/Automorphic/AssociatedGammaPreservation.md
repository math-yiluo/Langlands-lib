# Gamma preservation for the two Hecke families

Supporting module for the proof of `AssociatedGammaStatement` (module
`Langlands.Automorphic.AssociatedGammaPreservation`). It discharges the two preservation
inputs of the published two-twist engine (`InfinityGammaPreservation`,
`FiniteGammaPreservation`) for the automorphic and arithmetic Hecke families used in the proof
of `AssociatedGammaStatement` (Henniart 2000, Théorème 2.3: the twisting characters are trivial
at infinity and at the selected place `v`, where the local factors therefore do not change).
Internal deduction.

## Results

- `meromorphicEq_refl`: `MeromorphicEq f f`.
- `HeckeCharacter.finiteComponent_one`: the trivial Hecke character has trivial local
  components.
- `infinityGammaPreservation_families`: the archimedean factors of both families do not
  depend on the character (`localFactors_inl` of both setups).
- `finiteGammaPreservation_families`: if `χ_v = 1` then the factors at `v` equal those of the
  trivial character, because both families depend on the character only through its local
  component (`localFactors_inr_of_finiteComponent_eq`).
