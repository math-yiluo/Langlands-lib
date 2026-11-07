# Decomposition groups acting on isotypic parts of the cohomology of the actual CM tower

This internal construction restricts the Galois actions on the `ξ`-isotypic
parts of the cohomology of the actual geometric CM tower to the
decomposition group at a finite place `w` of the CM field `F`. That group is
the absolute Galois group of the actual completion `F_w`. The restriction
uses a specified embedding of algebraic closures. The construction covers
the shrinking-level cohomology, the prime-to-`m` cohomology and the Hecke
modules of `K'`-fixed vectors of the prime-to-`m` isotypic part. The
restricted action is the restriction of the Galois action on the isotypic
part, and changing the embedding is the action of the element of
`Gal(F̄/F)` relating the two embeddings. Unramifiedness passes from the
cohomology to its isotypic parts and their Hecke modules. The geometric
Frobenius endomorphisms commute with the inclusion of the isotypic part
and with the Hecke algebra. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313, part (iii), describes the action of
the decomposition group `Z_w = Gal(F̄_w/F_w)` on `H^{n-1}(S_K(N), W)[π]`.
Part (ii) uses the Frobenius eigenvalues at almost all unramified places,
through formula (5.6). This module constructs the restriction to these
decomposition groups of the Galois actions on the isotypic parts of the
published CM cohomology modules, and the Frobenius endomorphisms of the
Hecke modules of fixed vectors of the isotypic parts.

The coefficients are module sheaves on `Spec F`, pulled back to every
level. The module does not construct Harris's coefficient systems `W`, the
representation `JL(π_f)`, the Weil-group representations of (5.4) and
(5.5), or compactly supported or adic cohomology. `ξ` is an arbitrary
representation. The module proves no unramifiedness of the cohomology at
any place: the results about unramified actions take it as a hypothesis.
No topology on the Galois groups and no continuity of actions is
considered. No statement of Harris is formalized.

## Inputs

The CM data `E`, `F`, `L`, `D`, `C`, the named propositions `preservation`
through `htor`, `q : CMRepresentabilityStatement ...`, the inputs
`existence`, `geometry`, `hRigid` and `criterion`, and the commutative ring
`R : Type` are those of the published
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients` and
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`. Below `...`
abbreviates them. Write `base` for `Spec (CommRingCat.of F)`. Let
`U : Type uU` be an `R`-module, `w : Global.FinitePlace F`, and let `j k` be
elements of `ClosureEmbedding (NumberField.FinitePlace.embedding w)`.

The published modules provide `cmSmallLevelGaloisCohomologyFunctor ... R d`
and, for `m : ℕ`, `hm : m ≠ 0` and a level `K₀` of
`(D.rationalInvolution.DividingPoints m)ᵐᵒᵖ`,
`cmPrimeToGaloisCohomologyFunctor ... m hm K₀ ... R d` and, for a level `K'`
of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`,
`cmPrimeToGaloisHeckeModuleFunctor`. The published
`Langlands.Shimura.LevelHeckeModule` provides `LevelHecke.heckeModuleFunctor`
and `LevelHecke.heckeModuleActionFunctor`.

The module `Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology`
(candidate `24e3f602-b5d7-4c07-8a1d-4d8b67948758`, accepted and awaiting
publication) provides `cmSmallLevelDecompositionCohomologyFunctor ... R w d j`,
`cmSmallLevelDecompositionChangeIso`, `cmPrimeToDecompositionCohomologyFunctor`,
`cmPrimeToDecompositionChangeIso` and `cmPrimeToHeckeFrobenius`. Its generic
module `Langlands.Shimura.DecompositionGroupAction` provides
`localRestriction`, `localClosureChange`, `atFinitePlace`,
`IsUnramifiedAlong`, `geometricFrobenius`, `geometricFrobenius_eq_of_lift`,
`geometricFrobenius_naturality` and `geometricFrobenius_conj`.

The module `Langlands.Shimura.PEL.HarrisTaylorCMIsotypicCohomology`
(candidate `06482d9c-709f-449e-bd42-538102e24d51`, staged) provides
`cmSmallLevelIsotypicCohomologyFunctor ... R ξ d`,
`cmSmallLevelIsotypicCohomologyι`, `cmPrimeToIsotypicCohomologyFunctor`,
`cmPrimeToIsotypicCohomologyι` and `cmPrimeToIsotypicHeckeModuleFunctor`.
Its generic module `Langlands.Shimura.IsotypicGaloisAction` provides
`isotypicActionFunctor` and `isotypicMap`. The module
`Langlands.Shimura.IsotypicDecompositionAction`, submitted together with
this one, provides `isotypicAtFinitePlaceIso`, `IsUnramifiedAlong.mapAction`
and `IsUnramifiedAlong.isotypic`.

## The shrinking-level cohomology

Let `ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U`
and write `H d` for `cmSmallLevelGaloisCohomologyFunctor ... R d`.

- `cmSmallLevelIsotypicDecompositionFunctor ... R ξ w d j` is
  `cmSmallLevelDecompositionCohomologyFunctor ... R w d j` followed by
  `isotypicActionFunctor ξ (LocalGroup w)`. It is a functor from
  `ModuleSheaf base R` to
  `Action (SmoothRep R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) (LocalGroup w)`.
- `cmSmallLevelIsotypicDecompositionFunctor_ρ`: `g : LocalGroup w` acts by
  `isotypicMap ξ` of the action of `localRestriction w j g` on `(H d).obj M`,
  by `rfl`.
- `cmSmallLevelIsotypicDecompositionIso ... d j` is the natural isomorphism
  from this functor to `cmSmallLevelIsotypicCohomologyFunctor ... R ξ d`
  followed by `atFinitePlace _ w j`. It is `isotypicAtFinitePlaceIso`,
  between associators.
- `cmSmallLevelIsotypicDecompositionChangeIso ... d j k` is the natural
  isomorphism from the functor for `k` to the functor for `j`, obtained by
  whiskering `cmSmallLevelDecompositionChangeIso` with
  `isotypicActionFunctor`. Its component at `M` is `isotypicMap ξ` of the
  action of `localClosureChange w j k`
  (`cmSmallLevelIsotypicDecompositionChangeIso_hom_app_hom`).
- `cmSmallLevelIsotypicCohomology_isUnramifiedAlong`: if `(H d).obj M` is
  `IsUnramifiedAlong` at `w` and `j`, so is its `ξ`-isotypic part.
- `cmSmallLevelIsotypicCohomology_geometricFrobenius_ι`: the inclusion
  `cmSmallLevelIsotypicCohomologyι` intertwines the geometric Frobenius
  endomorphisms at `w` along `j` of the isotypic part and of `(H d).obj M`.

## The prime-to-`m` cohomology

Let `ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U` and
write `H' d` for `cmPrimeToGaloisCohomologyFunctor ... m hm K₀ ... R d`.

- `cmPrimeToIsotypicDecompositionFunctor ... R m hm K₀ ξ w d j` is
  `cmPrimeToDecompositionCohomologyFunctor ... R m hm K₀ w d j` followed by
  `isotypicActionFunctor ξ (LocalGroup w)`, with values in
  `Action (SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) (LocalGroup w)`.
- `cmPrimeToIsotypicDecompositionFunctor_ρ`,
  `cmPrimeToIsotypicDecompositionIso`,
  `cmPrimeToIsotypicDecompositionChangeIso` (with `_hom_app_hom`),
  `cmPrimeToIsotypicCohomology_isUnramifiedAlong` and
  `cmPrimeToIsotypicCohomology_geometricFrobenius_ι` are the analogues of
  the shrinking-level results, for `H' d` and
  `cmPrimeToIsotypicCohomologyFunctor`.

## Hecke modules and Frobenius

Let `K'` be a level of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`, and write
`I d` for `cmPrimeToIsotypicHeckeModuleFunctor ... R m hm K₀ ξ K' d`, the
`K'`-fixed vectors of the `ξ`-isotypic part as modules over
`LevelHecke.LevelHeckeAlgebra R K'.subgroup`, with the action of `Gal(F̄/F)`.

- `cmPrimeToIsotypicDecompositionHeckeModuleFunctor ... ξ w K' d j` is `I d`
  followed by `atFinitePlace _ w j`, with values in
  `Action (ModuleCat (LevelHecke.LevelHeckeAlgebra R K'.subgroup)) (LocalGroup w)`.
- `cmPrimeToIsotypicDecompositionHeckeModule_ρ_smul`: every
  `g : LocalGroup w` commutes with every element of the Hecke algebra, since
  it acts by a module map.
- `cmPrimeToIsotypicHeckeFrobenius ... d M j` is
  `DecompositionGroupAction.geometricFrobenius` of `(I d).obj M` along `j`:
  the endomorphism by which the chosen geometric Frobenius lift at `w` acts.
- `cmPrimeToIsotypicHeckeFrobenius_smul`: it commutes with every element of
  the Hecke algebra of `K'`.
- `cmPrimeToIsotypicHeckeModule_isUnramifiedAlong`: if `(H' d).obj M` is
  `IsUnramifiedAlong` at `w` and `j`, so is `(I d).obj M`. This applies
  `IsUnramifiedAlong.isotypic` and then `IsUnramifiedAlong.mapAction` for
  `LevelHecke.heckeModuleFunctor`.
- `cmPrimeToIsotypicHeckeFrobenius_eq_of_lift ... hM hg`: if `(I d).obj M`
  is `IsUnramifiedAlong` at `w` and `j`, and `g` satisfies
  `IsGeometricFrobeniusLift w g`, then `g` acts by
  `cmPrimeToIsotypicHeckeFrobenius`.
- `cmPrimeToIsotypicHeckeFrobenius_naturality ... α j`: a morphism
  `α : M ⟶ N` of module sheaves on `Spec F` intertwines the Frobenius
  endomorphisms through the induced Hecke-module map.
- `cmPrimeToIsotypicHeckeFrobenius_conj ... j k`: the Frobenius
  endomorphisms along `k` and `j` are conjugate by the action of
  `localClosureChange w j k`.
- `cmPrimeToIsotypicHeckeFrobenius_ι`: the map of Hecke modules induced by
  the inclusion `cmPrimeToIsotypicCohomologyι` through
  `LevelHecke.heckeModuleActionFunctor` intertwines
  `cmPrimeToIsotypicHeckeFrobenius` with `cmPrimeToHeckeFrobenius` of
  `HarrisTaylorCMDecompositionCohomology` on the Hecke module of `K'`-fixed vectors of
  the whole prime-to-`m` cohomology.

## Proof outline

Every functor is a functor of the decomposition-group or isotypic
constructions followed by `isotypicActionFunctor` or `atFinitePlace`. The
isomorphisms are whiskerings of `isotypicAtFinitePlaceIso` and of the
change-of-embedding isomorphisms. The descriptions of actions hold by
`rfl`. The remaining results are the generic results of
`DecompositionGroupAction` and `IsotypicDecompositionAction`, and the fact
that the actions are module maps.

## Provenance

This is an internal specialization of
`Langlands.Shimura.IsotypicDecompositionAction` to the Galois actions on
the isotypic parts of the cohomology of the actual geometric CM tower. No
action, isotypic part or Frobenius element is supplied as input. Harris
(1999), Theorem 5.7 (ii), (iii) and formula (5.6) on printed p. 313, is
motivation only.
