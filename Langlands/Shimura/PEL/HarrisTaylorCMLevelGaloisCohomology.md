# Galois actions on the cohomology of the actual CM tower at a fixed level

This internal construction applies `Langlands.Shimura.LevelAutomorphismAction`
to the published Galois action on the actual geometric CM tower. Fix a
sufficiently small CM level `U`. The Galois group of the CM field `F` then
acts on the étale cohomology `H^d(X_U ×_F Spec F̄, p_U^* M)` of a sheaf `M`
of `R`-modules on `Spec F` pulled back to the geometric CM scheme at the
level `U`. An element `σ` acts by pullback along its automorphism of the
algebraic-closure factor. The action is natural in `M`, and the insertion
of the level-`U` cohomology into the published colimit over all small
levels is Galois-equivariant. The same holds at the levels `K'` of the
prime-to-`m` tower, which are the levels `e⁻¹ (K₀ × K')` of the actual
tower. Over a topological field, a smooth finite-dimensional fixed-level
cohomology module is a continuous Galois representation of `F`, with its
Euler polynomials at unramified places. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, printed p. 312, introduces the cohomology `H^{n-1}(S_K(N), W)` of the
Shimura variety at the level `K(N)` and its `JL(π_f)`-isotypic component.
Theorem 5.7 on printed p. 313 describes the action of `Gal(F̄/F)` on it, and
part (ii) characterizes the resulting Galois representation by Frobenius
characteristic polynomials through formula (5.6). The published modules
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients` and
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology` construct the
Galois action only on the colimits over levels. This module constructs it at
each fixed level of the actual CM tower.

The coefficients are module sheaves on `Spec F`, pulled back to the level.
The module does not construct Harris's coefficient systems `W`, compactly
supported or adic cohomology, or Hecke operators at a fixed level. It does
not compare the fixed-level cohomology with the fixed vectors of the
colimit; that is the separate Library statement
`HarrisCMColimitInvariantsStatement`, which is not used. It does not compare
the action with the Galois action `EtaleGaloisAction.galoisCohomologyRep` on
the cohomology of base changes with constant coefficients, which is
constructed differently. Smoothness, finite dimension and unramifiedness are
hypotheses of the results about continuous Galois representations; none is
proved. No statement of Harris is formalized.

## Inputs

The CM data `E`, `F`, `L`, `D`, `C`, the named propositions `preservation`
through `htor` and `q : CMRepresentabilityStatement ...` are those of the
published `Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients`;
below `...` abbreviates them. The fixed-level constructions use no further
inputs. The comparisons with the colimits also use `existence`, `geometry`,
`hRigid` and `criterion`, through which the Library proves that the
transition maps of the tower are étale (`cmSmallLevelTowerEtale`,
`cmPrimeToTowerEtale`). Write `base` for `Spec (CommRingCat.of F)` and
`Gamma` for `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`, which is
definitionally `Field.absoluteGaloisGroup F`.

- From the published `HarrisTaylorCMSmallLevelGaloisCoefficients`:
  `cmGeometricSchemeTower`, `cmSmallLevelArithmeticGeometricStructure`
  (the projections `p_U` to `Spec F`), `cmSmallLevelGaloisAction`, which acts
  at each level by `EtaleGaloisAction.baseChangeMap` on the algebraic-closure
  factor (`cmSmallLevelGaloisAut_hom_app`), `cmSmallLevelGaloisAction_over`,
  `cmSmallLevelArithmeticCoefficients`, `cmSmallLevelGaloisCohomologyFunctor`
  and `cmSmallLevelGaloisCohomology_ρ_ι_apply`.
- From the published `HarrisTaylorCMPrimeToGaloisCohomology`:
  `cmPrimeToSchemeTower`, `cmPrimeToArithmeticStructure`,
  `cmPrimeToGaloisAction` (with `cmPrimeToGaloisAction_hom_app`),
  `cmPrimeToGaloisAction_over`, `cmPrimeToArithmeticCoefficients`,
  `cmPrimeToGaloisCohomologyFunctor` and
  `cmPrimeToGaloisCohomology_ρ_ι_apply`.
- From `Langlands.Shimura.LevelAutomorphismAction`, submitted together with
  this module: `levelActionFunctor`.
- From `Langlands.Shimura.ContinuousGaloisAction` (candidate
  `5c2f38db-a736-4706-aa12-6de9f8bf0b33`, accepted and awaiting
  publication): `toObjects`, `hasEulerPolynomialAt_toObjects_iff` and
  `hasEulerPolynomialAt_toObjects_iff_along`; and
  `FrobeniusPolynomial.frobeniusEulerPolynomial` from the same candidate.
- From the published `Langlands.Shimura.DecompositionGroupAction`:
  `IsUnramifiedAt`, `IsUnramifiedAlong` and `geometricFrobenius`.

## The shrinking-level tower at a fixed level

Let `R : Type` be a commutative ring and `U : SmallCMLevel D`.

- `cmLevelGaloisCohomologyFunctor ... R U d : ModuleSheaf base R ⥤ Action (ModuleCat R) Gamma`
  is `LevelAutomorphismAction.levelActionFunctor` for the projections
  `cmSmallLevelArithmeticGeometricStructure`, the action
  `cmSmallLevelGaloisAction` and the level `U`.
- `cmLevelGaloisCohomologyFunctor_obj_V`: its value at `M` has space
  `H^d(X̄_U, p_U^* M)`, that is,
  `(cohomology ((cmGeometricSchemeTower ...).obj U) R d).obj ((inverseImage (p.app U) R).obj M)`.
- `cmLevelGaloisCohomologyFunctor_ρ`: `σ` acts by
  `LevelTowerCohomology.projectionCohomologyMap` along
  `(cmSmallLevelGaloisAction ... σ).unop.hom.app U`.
- `cmLevelGaloisCohomology_ι_apply ... R U existence geometry hRigid criterion d M σ x`:
  the action of `σ` on `(cmSmallLevelGaloisCohomologyFunctor ... R d).obj M`
  sends the image under `RestrictedLevelColimit.ι` of a level-`U` class `x`
  to the image of the action of `σ` on `x`.

## The prime-to-`m` tower at a fixed level

Let `m : ℕ`, `hm : m ≠ 0`, `K₀` a level of
`(D.rationalInvolution.DividingPoints m)ᵐᵒᵖ` and `K'` an object of
`(cmPrimeToProperty D m hm K₀).FullSubcategory`.

- `cmPrimeToLevelGaloisCohomologyFunctor ... R m hm K₀ K' d`, with
  `_obj_V` and `_ρ`: the analogue for the prime-to-`m` tower
  `cmPrimeToSchemeTower` with its projections `cmPrimeToArithmeticStructure`
  and the action `cmPrimeToGaloisAction`, at the level `K'`.
- `cmPrimeToLevelGaloisCohomology_ι_apply`: the insertion of the level-`K'`
  cohomology into `(cmPrimeToGaloisCohomologyFunctor ... d).obj M` is
  Galois-equivariant.

## Continuous Galois representations at a fixed level

Let now `R : Type` be a field with a topology, `w : Global.FinitePlace F` and
`j` a closure embedding at `w`.

- `cmLevelGaloisRepresentation ... R U d M hsmooth`: if `hsmooth` proves that
  `((Rep.ActionToRep R (Field.absoluteGaloisGroup F)).obj ((cmLevelGaloisCohomologyFunctor ... R U d).obj M)).ρ`
  is smooth and the space is finite-dimensional over `R`, this is
  `ContinuousGaloisAction.toObjects` of the fixed-level action, an object of
  `Objects F R`. `_rank` gives its rank, the dimension of the cohomology
  module. `_hasEulerPolynomialAt_iff` says that it has Euler polynomial `P`
  at `w` if and only if the action is unramified at `w` with Frobenius Euler
  polynomial `P`. `_hasEulerPolynomialAt_of_isUnramifiedAlong hu` says that,
  if the action is `IsUnramifiedAlong` at `w` and `j`, the Euler polynomial
  at `w` is the reverse of the characteristic polynomial of its geometric
  Frobenius endomorphism along `j`.
- `cmPrimeToLevelGaloisRepresentation ... R m hm K₀ K' d M hsmooth`, with
  `_rank`, `_hasEulerPolynomialAt_iff` and
  `_hasEulerPolynomialAt_of_isUnramifiedAlong`: the same at the prime-to-`m`
  level `K'`.

## Proof outline

The fixed-level functors are instances of `levelActionFunctor`, and their
descriptions hold by `rfl`. The comparisons with the colimits are the
published lemmas `cmSmallLevelGaloisCohomology_ρ_ι_apply` and
`cmPrimeToGaloisCohomology_ρ_ι_apply`, whose right-hand sides are the
fixed-level actions. The statements about continuous Galois representations
apply `Langlands.Shimura.ContinuousGaloisAction`.

## Provenance

This is an internal specialization of
`Langlands.Shimura.LevelAutomorphismAction` to the published Galois actions
on the actual geometric CM tower and on its prime-to-`m` tower. No action or
Galois representation is supplied as input. Harris (1999), printed p. 312,
and Theorem 5.7 and formula (5.6) on printed p. 313, are motivation only.
