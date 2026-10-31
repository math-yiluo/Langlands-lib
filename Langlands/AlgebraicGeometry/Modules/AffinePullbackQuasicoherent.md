# Quasi-coherent pullback along a morphism of spectra

Fix commutative rings `R S : CommRingCat.{u}` in an arbitrary universe `u`
and a ring morphism `φ : R ⟶ S`. Put `p = Spec.map φ`.
For an actual quasi-coherent module sheaf `M : (Spec R).Modules`,
`Langlands.Scheme.Modules.affinePullbackTildeIso φ M` identifies

`p^*M ≅ (S ⊗_R Γ_R(M))^~`.

The tensor product here uses Mathlib's categorical scalar-extension convention,
`ModuleCat.extendScalars φ.hom`, and `Γ_R` is `moduleSpecΓFunctor`.
The map is constructed from the inverse of the pullback of the actual
tilde–global-sections counit `M.fromTildeΓ`, followed by the published
`tildePullbackIso` on `Γ_R(M)`. Mathlib proves this counit is an isomorphism
for every quasi-coherent sheaf on a spectrum.

`affinePullbackTildeIso_counit` states that precomposing this isomorphism's
forward map with `p^*(M.fromTildeΓ)` recovers `tildePullbackIso φ (Γ_R(M))`.
`affinePullbackTildeIso_naturality` states its coefficient naturality for any
morphism `a : M → N` of quasi-coherent sheaves. The target map is the tilde
of scalar extension of `Γ_R(a)`. Its proof cancels the invertible
`p^*(M.fromTildeΓ)`, uses naturality of the counit, and applies the published
naturality of `tildePullbackIso`.

Associated sheaves are quasi-coherent, and quasi-coherence is closed under
isomorphisms. Transporting it across this isomorphism gives the instance
`isQuasicoherent_affinePullback`: the actual module pullback between spectra
preserves quasi-coherence.

In namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`,
`isZero_higherDirectImage_affinePullback φ M q` then proves

`IsZero ((higherDirectImage p (q + 1)).obj (p^*M))`.

It applies the published
`affineQuasicoherentHigherDirectImageVanishing` to `p`, which is an affine
morphism, and the quasi-coherent module just obtained. Thus it supplies the
positive-degree pullback acyclicity input used by `baseChangeMap` and
`scalarBaseChangeMap` when the horizontal morphism is a morphism of spectra.
This corollary reuses the published affine vanishing proof.

These are internal consequences of the published `TildePullback` and
`AffineQuasicoherentHigherDirectImageVanishingProof` modules and the actual
tilde counit and quasi-coherence facts in pinned Mathlib
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`, commit
`5ed2965256430c3649e86755f9576b54eca72435`. No new external mathematical
assertion is used. There is no flatness, finiteness, nonzero-ring or
noetherian hypothesis. The result does not identify a cohomology base-change
map with an ordinary sections map and does not assert its invertibility,
higher cohomology base change on a nonaffine scheme, or the relative cube
theorem.
