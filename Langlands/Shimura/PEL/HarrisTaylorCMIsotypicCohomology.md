# Isotypic parts and multiplicity spaces of the cohomology of the actual CM tower

This internal construction applies the generic isotypic parts and
multiplicity spaces of `Langlands.Shimura.IsotypicGaloisAction` to the
published Galois actions on the cohomology of the actual geometric CM tower.
It covers the shrinking-level cohomology, with a representation `ξ` of
`GG(A_f)ᵐᵒᵖ`, and the prime-to-`m` cohomology, with a representation `ξ` of
`GG(A_f^{(m)})ᵐᵒᵖ`. The `ξ`-isotypic part keeps the restricted actions of
the finite-adelic group and of `Gal(F̄/F)`, and the multiplicity space
`Hom(ξ, -)` is a representation of `Gal(F̄/F)` by composition. Both are
natural in the coefficient sheaf. Evaluation `ξ ⊗ Hom(ξ, H) → H[ξ]` is
surjective and Galois-equivariant. In the prime-to-`m` case, the fixed
vectors of the isotypic part under a level `K'` are modules over the Hecke
algebra of `K'` with the commuting Galois action. All declarations are in
namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, printed p. 312, writes `H^{n-1}(S_K(N), W)[π]` for the
`JL(π_f)`-isotypic component of the cohomology of the Shimura variety, and
Theorem 5.7 on printed p. 313 describes the action of `Gal(F̄/F)` and of the
decomposition groups on it. Formulas (5.2), (5.3) and (5.5) on printed
pp. 312-313 use spaces of intertwining maps of representations. This module
constructs the isotypic parts and multiplicity spaces of the published CM
cohomology modules, for arbitrary representations `ξ`, with their Galois
actions.

The coefficients are module sheaves on `Spec F`, pulled back to every level.
The module does not construct Harris's coefficient systems `W`, the
representation `JL(π_f)`, or compactly supported or adic cohomology. No
irreducibility, admissibility or smoothness of `ξ` is assumed, and nothing
is proved about the isotypic parts beyond the stated results. No topology on
the Galois group and no continuity of its action is considered. Harris's
statements are motivation only; none is formalized.

## Inputs

The CM data `E`, `F`, `L`, `D`, `C`, the named propositions `preservation`
through `htor`, `q : CMRepresentabilityStatement ...`, the inputs
`existence`, `geometry`, `hRigid` and `criterion`, and the commutative ring
`R : Type` are those of the published
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients` and
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`. Below `...`
abbreviates them. Write `Gamma` for
`AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F` and `base` for
`Spec (CommRingCat.of F)`. Let `U : Type uU` be an `R`-module.

The published `HarrisTaylorCMSmallLevelGaloisCoefficients` provides
`cmSmallLevelGaloisCohomologyFunctor ... R d`, a functor from
`ModuleSheaf base R` to
`Action (SmoothRep R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) Gamma`.
For `m : ℕ`, `hm : m ≠ 0` and a level `K₀` of
`(D.rationalInvolution.DividingPoints m)ᵐᵒᵖ`, the published
`HarrisTaylorCMPrimeToGaloisCohomology` provides
`cmPrimeToGaloisCohomologyFunctor ... m hm K₀ ... R d`, with values in
`Action (SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) Gamma`. The
published `Langlands.Shimura.LevelHeckeModule` provides
`LevelHecke.heckeModuleActionFunctor R Gamma K`, the `K`-fixed vectors as
modules over `LevelHecke.LevelHeckeAlgebra R K` with the induced action of
`Gamma`, and `LevelHecke.heckeModuleActionFunctor_ρ_smul`.

The module `Langlands.Shimura.IsotypicGaloisAction`, submitted together with
this one, provides `isotypicObj`, `isotypicMap`, `isotypicActionFunctor`,
`isotypicActionι`, `isotypicι_app_injective`, `multiplicityRepFunctor`,
`multiplicityRepresentation`, `isotypicGaloisRepresentation`,
`isotypicEvaluation`, `isotypicEvaluation_surjective` and
`isotypicEvaluation_galois`. The published
`Langlands.Cohomology.HyperextDegenerationIsotypic` provides
`isotypicPart`.

## The shrinking-level cohomology

Let `ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U` and
write `H d` for `cmSmallLevelGaloisCohomologyFunctor ... R d`.

- `cmSmallLevelIsotypicCohomologyFunctor ... R ξ d` is `H d` followed by
  `isotypicActionFunctor ξ Gamma`, a functor from `ModuleSheaf base R` to
  `Action (SmoothRep R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) Gamma`.
- `cmSmallLevelIsotypicCohomologyFunctor_obj_V` and
  `cmSmallLevelIsotypicCohomologyFunctor_ρ`: the underlying smooth
  representation at `M` is `isotypicObj ξ ((H d).obj M).V`, and `σ : Gamma`
  acts by `isotypicMap ξ (((H d).obj M).ρ σ)`, by `rfl`.
- `cmSmallLevelIsotypicCohomologyι ... R ξ d` is the natural transformation
  to `H d` given by `isotypicActionι`, equivariant for both groups.
  `cmSmallLevelIsotypicCohomologyι_app_apply` states that it sends `x` to
  `x.1`, and `cmSmallLevelIsotypicCohomologyι_app_injective` that its
  components are injective.
- `cmSmallLevelMultiplicityFunctor ... R ξ d` is `H d` followed by
  `multiplicityRepFunctor ξ Gamma`, a functor from `ModuleSheaf base R` to
  `Rep R Gamma`. `cmSmallLevelMultiplicityFunctor_ρ_apply` states that
  `σ` sends an intertwining map `φ` to its composition with the action of
  `σ` on the cohomology, by `rfl`.
- `cmSmallLevelIsotypicEvaluation_surjective`: evaluation
  `isotypicEvaluation ξ ((H d).obj M).V` is surjective.
- `cmSmallLevelIsotypicEvaluation_galois`: evaluation composed with
  `LinearMap.lTensor U` of the action of `σ` on the multiplicity space
  equals the action of `σ` on the isotypic part composed with evaluation.

## The prime-to-`m` cohomology

Let `ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U` and
write `H' d` for `cmPrimeToGaloisCohomologyFunctor ... m hm K₀ ... R d`.

- `cmPrimeToIsotypicCohomologyFunctor ... R m hm K₀ ξ d` is `H' d`
  followed by `isotypicActionFunctor ξ Gamma`, with values in
  `Action (SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) Gamma`.
- `cmPrimeToIsotypicCohomologyFunctor_obj_V`,
  `cmPrimeToIsotypicCohomologyFunctor_ρ`,
  `cmPrimeToIsotypicCohomologyι`, `cmPrimeToIsotypicCohomologyι_app_apply`
  and `cmPrimeToIsotypicCohomologyι_app_injective` are the analogues of the
  shrinking-level results.
- `cmPrimeToMultiplicityFunctor ... R m hm K₀ ξ d` is `H' d` followed by
  `multiplicityRepFunctor ξ Gamma`, with `cmPrimeToMultiplicityFunctor_ρ_apply`.
- `cmPrimeToIsotypicEvaluation_surjective` and
  `cmPrimeToIsotypicEvaluation_galois` are the analogues of the
  shrinking-level evaluation results.

## Hecke modules

Let `K'` be a level of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`.

- `cmPrimeToIsotypicHeckeModuleFunctor ... R m hm K₀ ξ K' d` is
  `cmPrimeToIsotypicCohomologyFunctor ... ξ d` followed by
  `LevelHecke.heckeModuleActionFunctor R Gamma K'.subgroup`, with values in
  `Action (ModuleCat (LevelHecke.LevelHeckeAlgebra R K'.subgroup)) Gamma`:
  the `K'`-fixed vectors of the `ξ`-isotypic part as modules over the Hecke
  algebra of `K'`, with the action of `Gamma`.
- `cmPrimeToIsotypicHeckeModule_ρ_smul`: the action of every `σ : Gamma`
  commutes with every element of `LevelHecke.LevelHeckeAlgebra R K'.subgroup`.
  It is `LevelHecke.heckeModuleActionFunctor_ρ_smul`.

## Proof outline

Every functor is a published Galois cohomology functor followed by a
generic functor of `IsotypicGaloisAction` or the published Hecke-module
functor. The descriptions of objects and actions hold by `rfl`, and the
remaining results are the generic results of `IsotypicGaloisAction` and
`LevelHeckeModule` at these objects.

## Provenance

This is an internal specialization of `Langlands.Shimura.IsotypicGaloisAction`
to the published Galois actions on the cohomology of the actual geometric
CM tower. No action, isotypic part or Hecke module is supplied as input.
Harris (1999), printed pp. 312-313, the definition of
`H^{n-1}(S_K(N), W)[π]`, formulas (5.2)-(5.5) and Theorem 5.7, is
motivation only.
