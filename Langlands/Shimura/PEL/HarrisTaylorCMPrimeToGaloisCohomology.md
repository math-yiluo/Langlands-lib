# Galois action and Hecke modules on the prime-to-`m` cohomology of the actual CM tower

This internal construction equips the prime-to-`m` cohomology of
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology` with the Galois action
of the published `Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients`.
The Galois automorphisms of the actual geometric CM tower over `Spec F`
restrict to the prime-to-`m` tower `K' ↦ Sh(e⁻¹ (K₀ × K'))`. On its colimit
cohomology with coefficients pulled back from `Spec F` they act by
pullback. This action commutes with the action of
`GG(A_f^{(m)})ᵐᵒᵖ` and with the comparison to the shrinking-level cohomology
of the CM tower. The `K'`-fixed vectors for a prime-to-`m` level `K'` are
modules over the Hecke algebra of `K'` with the commuting Galois action. All
declarations are in namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Proposition 4.10 on printed p. 311, asks for its spectral sequences
to be `GG(A_f^{ℓ,p})`-equivariant as the level `K(N)^{ℓ,p}` varies, with the
component at `ℓ, p` fixed. The cohomology there carries Galois and Hecke
actions. This module gives the corresponding structure on the prime-to-`m`
cohomology with the fixed component `K₀` at the places dividing `m`.

The coefficients are module sheaves on `Spec F`, pulled back to every level.
The module does not construct the nonconstant Harris coefficient systems,
adic limits, spectral sequences or compactly supported cohomology. It
considers no topology on the Galois group and no continuity of its action.
The rational involution of `D` and its prime-to-`m` points are not identified
with Harris's group and `GG(A_f^{ℓ,p})`. Harris's passage is motivation
only; no statement from it is formalized.

## Inputs

The CM data `E`, `F`, `L`, `D`, `C`, the named propositions `preservation`
through `htor`, and `q : CMRepresentabilityStatement ...` are those of the
published `HarrisTaylorCMSmallLevelGaloisCoefficients`. Write `Fbar` for
`AlgebraicClosure F`, `Gamma` for `Fbar ≃ₐ[F] Fbar`, `small` for
`D.rationalInvolution.LevelSufficientlySmall`, and `base` for
`Spec (CommRingCat.of F)`. That module provides the projection
`cmSmallLevelArithmeticGeometricStructure` of the actual geometric CM tower
`cmGeometricSchemeTower ... q` to `Spec F`, the Galois action
`cmSmallLevelGaloisAction : Gamma →* (Aut (cmGeometricSchemeTower ... q))ᵐᵒᵖ`
with `cmSmallLevelGaloisAction_over` and `cmSmallLevelGaloisAut_hom_app`
(the component at a level `U` is
`EtaleGaloisAction.baseChangeMap (cmSmallLevelArithmeticStructure.app U) σ`).
Under the inputs `existence`, `geometry`, `hRigid` and `criterion` it provides
`cmSmallLevelArithmeticCoefficients ... R M` and
`cmSmallLevelGaloisCohomologyFunctor ... R d`, a functor from
`ModuleSheaf base R` to
`Action (SmoothRep R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) Gamma`.

Let `m : ℕ`, `hm : m ≠ 0` and `K₀` a level of
`(D.rationalInvolution.DividingPoints m)ᵐᵒᵖ`. The module
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`, from an earlier
accepted submission, provides the splitting `cmPrimeToSplit D m hm`, written
`e` here, the property `cmPrimeToProperty D m hm K₀` of prime-to-`m` levels,
the prime-to-`m` tower `cmPrimeToSchemeTower ... q m hm K₀` with
`cmPrimeToSchemeTower_restrictedSelfArrow`, and, under the further inputs,
`cmPrimeToTowerEtale`, `cmPrimeToCoefficientDiagram`,
`cmPrimeToTrivialCoefficients`, `cmPrimeToCoefficients`,
`cmPrimeToSmoothCohomology` and `cmPrimeToCohomologyComparison`.

The module `Langlands.Shimura.RestrictedReindexTowerAutomorphisms`, submitted
together with this one, provides `awayAutomorphisms`,
`awayAutomorphisms_over` and `automorphism_awayComparison_apply`. The
published `RestrictedReindexLevelTowerCohomology.reindexProjection`,
`RestrictedSplitLevelTowerCohomology.awayCoefficients_canonical`, and the
published `RestrictedLevelTowerCohomology.canonicalCoefficients`,
`isLevelTrivialCoefficients_canonical`, `smoothCanonicalCohomologyFunctor`,
`smoothCanonicalPullback`, `canonicalPullback_ι` and
`automorphismActionFunctor` are used. The published
`Langlands.Shimura.LevelHeckeModule` provides
`LevelHecke.restrictedAutomorphismHeckeModuleFunctor`,
`heckeModuleActionFunctor`, `heckeModuleActionForgetIso` and
`doubleCoset_smul_heckeActionNatTrans`; the published
`Langlands.Shimura.LevelHeckeAction` provides `fixedVectorsActionFunctor`
and `heckeActionNatTrans`, and the published
`Langlands.Shimura.LevelHeckeAlgebra` provides `LevelHeckeAlgebra` and
`doubleCoset`.

## The Galois action on the prime-to-`m` tower

- `cmPrimeToArithmeticStructure ... q m hm K₀` is the projection of the
  prime-to-`m` tower to `Spec F`: the published `reindexProjection` along
  `awayOver e K₀` of `cmSmallLevelArithmeticGeometricStructure`.
  `cmPrimeToArithmeticStructure_app` states that its component at `K'` is the
  projection of the actual geometric CM scheme at the level
  `(awayFunctor e small K₀).obj K'`, that is, `e⁻¹ (K₀ × K')`, by `rfl`.
- `cmPrimeToGaloisAction ... q m hm K₀ : Gamma →* (Aut (cmPrimeToSchemeTower ... q m hm K₀))ᵐᵒᵖ`
  is `awayAutomorphisms e K₀ cmSmallLevelGaloisAction`, the restriction of the
  Galois action to the prime-to-`m` tower.
- `cmPrimeToGaloisAction_hom_app ... σ K'`: at level `K'`, `σ` acts by
  `EtaleGaloisAction.baseChangeMap` of the arithmetic projection at level
  `e⁻¹ (K₀ × K')`. It is `cmSmallLevelGaloisAut_hom_app`.
- `cmPrimeToGaloisAction_over ... σ`: these automorphisms lie over `Spec F`
  for `cmPrimeToArithmeticStructure`. It is `awayAutomorphisms_over` applied to
  `cmSmallLevelGaloisAction_over`.

## Arithmetic coefficients and the Galois action on cohomology

Assume the inputs `existence`, `geometry`, `hRigid` and `criterion`, and let
`R : Type` be a commutative ring and `M : ModuleSheaf base R`. The étaleness
of the level maps of the prime-to-`m` tower is installed from
`cmPrimeToTowerEtale`, and the finite dimensionality of the algebra over `ℚ`
is derived from `D.finite` as in the published CM modules.

- `cmPrimeToArithmeticCoefficients ... R M` is
  `canonicalCoefficients R (cmPrimeToArithmeticStructure ...) M`, the sheaf
  `M` pulled back to every level of the prime-to-`m` tower.
- `cmPrimeToArithmeticCoefficients_eq`: these are
  `cmPrimeToCoefficients ... R (cmSmallLevelArithmeticCoefficients ... R M)`,
  the arithmetic coefficients of the CM tower restricted to the levels
  `e⁻¹ (K₀ × K')`. It is `awayCoefficients_canonical`.
- `cmPrimeToArithmeticCoefficients_trivial`: they satisfy
  `cmPrimeToTrivialCoefficients`, by `isLevelTrivialCoefficients_canonical`
  and `cmPrimeToSchemeTower_restrictedSelfArrow`.
- `cmPrimeToArithmeticCohomologyFunctor ... R d` is
  `smoothCanonicalCohomologyFunctor` for the prime-to-`m` tower, a functor
  from `ModuleSheaf base R` to
  `SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`.
  `cmPrimeToArithmeticCohomologyFunctor_obj` states that its value at `M` is
  `cmPrimeToSmoothCohomology` of `cmPrimeToArithmeticCoefficients ... R M`,
  by `rfl`.
- `cmPrimeToGaloisCohomologyFunctor ... R d` is the published
  `automorphismActionFunctor` for the prime-to-`m` tower, its projection and
  `cmPrimeToGaloisAction`. It is a functor from `ModuleSheaf base R` to
  `Action (SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) Gamma`.
  `cmPrimeToGaloisCohomologyFunctor_obj_V` and
  `cmPrimeToGaloisCohomologyForgetIso` (the identity isomorphism) identify
  its underlying smooth representations with
  `cmPrimeToArithmeticCohomologyFunctor`.
- `cmPrimeToGaloisCohomologyFunctor_ρ`: `σ` acts by the published
  `smoothCanonicalPullback` along its automorphism of the prime-to-`m` tower,
  by `rfl`.
- `cmPrimeToGaloisCohomology_ρ_ι_apply ... σ K' x`: on a class `x` of level
  `K'`, the action of `σ` is the colimit leg at `K'` of the cohomological
  pullback `LevelTowerCohomology.projectionCohomologyMap` along the component
  of the automorphism at `K'`. It is `canonicalPullback_ι` evaluated at `x`.
- `cmPrimeToGaloisCohomology_commutes ... σ g x`: the action of `σ` commutes
  with the action of every `g : (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`.
  It is the intertwining property of the morphism of smooth representations
  by which `σ` acts.
- `cmPrimeToGaloisCohomologyComparison_apply ... σ x`: the comparison
  `cmPrimeToCohomologyComparison ... R (cmSmallLevelArithmeticCoefficients ... R M) d`
  to the shrinking-level cohomology sends the action of `σ` on `x` to the
  action of `σ` in `cmSmallLevelGaloisCohomologyFunctor ... R d`. It is
  `automorphism_awayComparison_apply`.

## Hecke modules

Let `K'` be a level of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`; it need
not satisfy `cmPrimeToProperty D m hm K₀`.

- `cmPrimeToGaloisHeckeModuleFunctor ... R K' d` is
  `LevelHecke.restrictedAutomorphismHeckeModuleFunctor` for the prime-to-`m`
  tower, its projection and `cmPrimeToGaloisAction`. It is a functor from
  `ModuleSheaf base R` to
  `Action (ModuleCat (LevelHecke.LevelHeckeAlgebra R K'.subgroup)) Gamma`: the
  `K'`-fixed vectors of the prime-to-`m` cohomology, as a module over the
  Hecke algebra of `K'`, with the action of `Gamma`.
- `cmPrimeToGaloisHeckeModuleFunctor_eq`: it is
  `cmPrimeToGaloisCohomologyFunctor ... R d` followed by
  `LevelHecke.heckeModuleActionFunctor R Gamma K'.subgroup`, by `rfl`.
- `cmPrimeToGaloisHeckeModuleForgetIso`: restricting the scalars from the
  Hecke algebra to `R` gives
  `cmPrimeToGaloisCohomologyFunctor ... R d` followed by
  `LevelHecke.fixedVectorsActionFunctor R Gamma K'.subgroup`. It is built
  from `heckeModuleActionForgetIso`.
- `cmPrimeToGaloisHeckeModule_ρ_smul ... σ a x`: the action of `σ` commutes
  with every `a : LevelHecke.LevelHeckeAlgebra R K'.subgroup`, since it is a
  Hecke-module map.
- `cmPrimeToGaloisHeckeModule_doubleCoset_smul ... g x`: for a `K'`-fixed
  vector `x`, the element `LevelHecke.doubleCoset K' g` of the Hecke algebra
  acts on `x` as the component of `LevelHecke.heckeActionNatTrans R Gamma K' K' g`
  at `(cmPrimeToGaloisCohomologyFunctor ... R d).obj M`, the double-coset
  operator `[K' g K']`. It is `doubleCoset_smul_heckeActionNatTrans`.

## Proof outline

Every declaration specializes a generic declaration to the prime-to-`m`
tower of the actual geometric CM tower: the away automorphisms of
`RestrictedReindexTowerAutomorphisms`, the canonical coefficients and
automorphism actions of `RestrictedLevelTowerCanonicalCoefficients`, and the
Hecke modules of `LevelHeckeModule`. The étaleness and finiteness instances
are installed locally as described above.

## Provenance

This is an internal specialization of published and submitted generic
constructions to the actual geometric CM tower, its Galois action and its
prime-to-`m` cohomology. No action, comparison or Hecke structure is supplied
as input. Harris (1999), Proposition 4.10 on printed p. 311, is motivation
only.
