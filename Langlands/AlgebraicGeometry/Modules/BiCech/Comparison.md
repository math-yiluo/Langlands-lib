# The bi-Čech complex computes relative cohomology

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.Comparison`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

Let `π : P ⟶ Spec R` be separated, `𝒲 : BiCover P`, and `F` a quasi-coherent module sheaf
on `P`. Assume `hW`: every open `biOpen 𝒲 s t` is affine.

- `isZero_relativeCohomology_term π 𝒲 F hW i n`: the terms of the bi-Čech complex satisfy
  `IsZero ((relativeCohomology π (n + 1)).obj (term 𝒲 F i))`. Each summand
  `sheafOn F W` with `W` affine is acyclic by the Library's
  `CechResolution.isZero_relativeCohomology_sheafOn`. Right derived functors are additive
  (`CechResolution.rightDerived_additive`), so a finite biproduct of acyclic modules is
  acyclic (`CechResolution.isZero_obj_biproduct`).
- `nonempty_relativeCohomology_iso_bicech_homology π 𝒲 F hW n`: there is an isomorphism
  `(relativeCohomology π n).obj F ≅ (Γ_R(bicechComplex 𝒲 F)).homology n`. Here `Γ_R` is
  `DerivedSections.relativeGlobalSections π` applied termwise. The augmentation is a
  quasi-isomorphism (`quasiIso_bicechAug`) and the terms are acyclic, so the Library's
  `CechResolution.isIso_derivedResolutionComparison` gives an isomorphism in the derived
  category. Worker 1137's `CechResolution.rightDerivedObjIsoHomologyOfDerivedIso` turns it
  into the stated isomorphism of cohomology modules.

Provenance: internal; this is the acyclic-resolution computation of derived functors.
