# Čech groups of the FLT port and actual cohomology

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.CechHSuccBridge` (namespace
`Langlands.AlgebraicGeometry.Modules.CechBridge`) connects the Čech cohomology of presheaves of
modules in the Library's port of the Anthropic FLT formalization (`OModulePresheaf`, with groups
`HSucc K n` defined as kernels modulo images of the alternating Čech differential) to the Library's
actual cohomology `DerivedSections.relativeCohomology`. It contains only internal helper
declarations.

- `cechComplex F K`: the `ℕ`-indexed Čech cochain complex of an FLT presheaf `F` for an ordered
  affine cover `K` (`CochainComplex.of` the cochain modules and differentials).
  `cechComplex_d` records its differential.
- `homologySuccEquiv F K n`: `H^{n+1}(cechComplex F K) ≃ F.HSucc K n`. This generalises the
  private `cechHomologySuccEquiv` of the Library proof `ProperCoherentCohomologyFiniteProof` from
  sections presheaves to arbitrary FLT presheaves. The isomorphism goes through
  `HomologicalComplex.homologyIsoSc'` and `ShortComplex.moduleCatHomologyIso`.
- `hsuccEquivRelativeCohomology K M n`: for `π` separated and `M` quasi-coherent,
  `(ofModules π M).HSucc K n ≃ Hⁿ⁺¹(X, M)`. The Čech complex of the sections presheaf is the
  Library's `cechCochainComplex`, and the Library's `CechResolution.cechCohomologyIso` identifies
  its homology with actual cohomology.
- `cechComplexIsoOfBijective`, `hsuccEquivOfBijective`: an FLT morphism of presheaves on affine
  opens (`AffHom`) that is bijective on every intersection `K.affineInter π s` of the cover induces
  an isomorphism of Čech complexes (`HomologicalComplex.Hom.isoOfComponents`, from the FLT
  `AffHom.cochainMap` and `cochainMap_comp_d`), hence of all `HSucc` groups.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
