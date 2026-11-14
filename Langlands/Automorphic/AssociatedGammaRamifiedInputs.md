# Local inputs of the stable comparison at ramified places

Supporting module of Task 5003 (module
`Langlands.Automorphic.AssociatedGammaRamifiedInputs`). It checks, at a finite place `z`,
the hypotheses of the published `StableTwistPairGammaMatchStatement` (Henniart 1986,
Lemma 4.2) for the local classes of a cuspidal pair and the local restrictions of weakly
associated relative Weil representations, as used at the bad places in the proof of
`AssociatedGammaStatement` (Henniart 2000, Théorème 2.3). Internal deductions.

## Results

- `localPairClass_twist_eq_twistClass`: along a local relative Weil map, the class of
  `((χ ∘ τ_F) ⊗ S)` is `twistClass (weilCharacter e χ_z) (localPairClass S ι)`, with `e` the
  base candidate of a normalized family (`localPairClass_twist_eq`,
  `reciprocityCharacter_apply_localMap`).
- `lt_multiplicativeConductor_quasicharacterBase`: a local character nontrivial on the
  principal units of level `r` has conductor `> r` (the published
  `lt_multiplicativeConductor_of_nontrivialOnPrincipalUnits` at `padicFieldAt z rfl`).
- `determinantCharacter_localComponent`: if `det S = ω ∘ τ_F` (`reciprocityCharacter`), the
  determinant of the local restriction is `weilCharacter e ω_z`.
- `localComponent_scalar_of_hasCentralCharacter`: if the realization has central character
  `ω`, the scalar `a` at `z` acts on every local component by `ω_z(a)`. The local scalar is
  the adelic scalar of the idele `a` at `z` (`scalar_finiteIdeleInclusion`); scalars commute,
  and the central-character condition on forms applies because the local component lies in
  the realization (`localComponent_le_full`).
- `centralActsBy_localClass`: hence `CentralActsBy` for the local class with `ω_z`.
