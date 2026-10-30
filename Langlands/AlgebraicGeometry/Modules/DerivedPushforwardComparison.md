# Actual derived sections along an acyclic pushforward

This internal construction specializes the Library's actual derived composite
comparison to sheaves of modules on schemes. It works in every universe `u`,
for arbitrary schemes `X` and `Y`, a morphism `h : X ⟶ Y`, a commutative ring
`R`, and a morphism `g : Y ⟶ Spec R`. All derived categories use Mathlib's
standard construction, as in `UniversalPerfectSectionsStatement`.

For an actual module `M` on `X` whose positive higher direct images along `h`
vanish, `DerivedSections.derivedPushforwardComparison h g M hM` is a morphism
in the unbounded derived category of `R`-modules from actual derived sections
of `M` over `h ≫ g` to actual derived sections of `h_* M` over `g`. Here actual
derived sections mean the published `DerivedPlus.derivedComplex` of
`DerivedSections.relativeGlobalSections`, followed by `DerivedCategory.Plus.ι`.
The morphism is precisely `AcyclicResolution.derivedCompComparison` for
pushforward along `h`, relative global sections along `g`, and the published
`relativeGlobalSectionsCompIso h g`.

`derivedPushforwardComparison_naturality` specializes the published coefficient
naturality to a morphism between any two coefficients satisfying the vanishing
condition. `derivedPushforwardComparison_homology` specializes the published
cohomology formula: in each degree `n : ℕ`, the homology map, followed by the
target's specified `DerivedPlus.homologyIso`, equals the source's specified
`DerivedPlus.homologyIso` followed by the published
`DerivedSections.pushforwardComparison h g M hM n`. This identifies the
specified morphism, including its transporting isomorphisms.

`isIso_derivedPushforwardComparison` applies the published theorem
`AcyclicResolution.derivedCompositeIsomorphism`. Both functors are left exact.
The theorem's remaining condition, that pushforwards of injectives are acyclic
for relative global sections, is supplied by the relative component of the
published `Modules.pushforwardInjectiveAcyclic`. Thus no further injective
acyclicity premise is imposed on the caller. `derivedPushforwardComparisonIso`
packages that same morphism as an isomorphism using `asIso`; its hom equality
is definitional.

For affine `h` and quasi-coherent `M`,
`affineDerivedPushforwardComparisonIso h g hAffine M hQC` supplies the
coefficient vanishing by the published theorem
`Modules.affineQuasicoherentHigherDirectImageVanishing`. It requires no
vanishing premise from the caller. The hom equality, naturality in
quasi-coherent coefficients, and nonnegative-cohomology formula are included
as the corresponding `affineDerivedPushforwardComparisonIso_hom` lemmas.
They follow directly from the general construction and its two identities.

The provenance is an internal specialization of the already proved formal
constructions in `AcyclicResolution.DerivedCompositeComparison`,
`AcyclicResolution.DerivedCompositeIsomorphismProof`,
`Modules.PushforwardComparison`, `Modules.PushforwardInjectiveAcyclicProof`,
and `Modules.AffineQuasicoherentHigherDirectImageVanishingProof`. This file
uses their proved results and makes no additional external mathematical
claim. It supplies neither a perfect representative nor compatibility with
geometric scalar base change; those remain separate obligations in the
universal-perfect-sections development.
