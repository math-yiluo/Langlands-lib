# Decomposition groups acting on the cohomology of the actual CM tower

This internal construction restricts the Galois actions on the cohomology of
the actual geometric CM tower to the decomposition group at a finite place
`w` of the CM field `F`, the absolute Galois group of the actual completion
`F_w`. The restriction uses a specified embedding of algebraic closures, and
changing the embedding is the action of the element of `Gal(F̄/F)` relating
the two embeddings. The construction covers three objects: the
shrinking-level cohomology, the prime-to-`m` cohomology, and the Hecke
modules of `K'`-fixed vectors. The restricted actions commute with the
finite-adelic actions, with the comparison between the two cohomologies and
with the Hecke algebra. The geometric Frobenius endomorphisms at `w` also
commute with the Hecke algebra. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313, part (iii), describes the action of
the decomposition group `Z_w = Gal(F̄_w/F_w)` on `H^{n-1}(S_K(N), W)[π]`.
Part (ii) and formula (5.6) use the eigenvalues of a geometric Frobenius at
almost all unramified places `w`. This module constructs the restriction of
the Galois actions of the published CM cohomology modules to these
decomposition groups, and the Frobenius endomorphisms of the Hecke modules
of fixed vectors.

The coefficients are module sheaves on `Spec F`, pulled back to every level.
The module does not construct Harris's coefficient systems `W`, the
`π`-isotypic parts, the Weil-group representations of (5.4) and (5.5), or
compactly supported or adic cohomology. It proves no unramifiedness of the
cohomology at any place; the Frobenius results that need it take
unramifiedness as a hypothesis. No topology on the Galois groups and no
continuity of actions is considered. Harris's theorem is motivation only;
no statement from it is formalized.

## Inputs

The CM data `E`, `F`, `L`, `D`, `C`, the named propositions `preservation`
through `htor`, `q : CMRepresentabilityStatement ...`, the inputs
`existence`, `geometry`, `hRigid` and `criterion`, and the commutative ring
`R : Type` are those of the published
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients` and
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`. Below `...`
abbreviates them. Write `Gamma` for `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`, the
group `Field.absoluteGaloisGroup F`, and `base` for `Spec (CommRingCat.of F)`.

The published `HarrisTaylorCMSmallLevelGaloisCoefficients` provides
`cmSmallLevelArithmeticCoefficients ... R M` and
`cmSmallLevelGaloisCohomologyFunctor ... R d`, a functor from
`ModuleSheaf base R` to
`Action (SmoothRep R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) Gamma`.
For `m : ℕ`, `hm : m ≠ 0` and a level `K₀` of
`(D.rationalInvolution.DividingPoints m)ᵐᵒᵖ`, the published
`HarrisTaylorCMPrimeToCohomology` provides `cmPrimeToCohomologyComparison`,
and the published `HarrisTaylorCMPrimeToGaloisCohomology` provides
`cmPrimeToGaloisCohomologyFunctor ... m hm K₀ ... R d`, with values in
`Action (SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) Gamma`, with
`cmPrimeToGaloisCohomologyComparison_apply`, and, for a level `K'` of
`(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`,
`cmPrimeToGaloisHeckeModuleFunctor ... R K' d`, with values in
`Action (ModuleCat (LevelHecke.LevelHeckeAlgebra R K'.subgroup)) Gamma`. It is
`cmPrimeToGaloisCohomologyFunctor` followed by the published
`LevelHecke.heckeModuleActionFunctor`, Mathlib's `Functor.mapAction` of the
published `LevelHecke.heckeModuleFunctor`.

The module `Langlands.Shimura.DecompositionGroupAction`, submitted together
with this one, provides `localRestriction`, `localClosureChange`,
`atFinitePlace`, `atFinitePlaceChangeIso`, `mapActionResIso`,
`IsUnramifiedAlong`, `geometricFrobenius`, `geometricFrobenius_eq_of_lift`,
`geometricFrobenius_naturality` and `geometricFrobenius_conj`. The published
`Langlands.Galois.ClosureRestriction` provides `ClosureEmbedding`, and the
published `Langlands.Galois.CompatibleFamily` provides `LocalGroup w`, the
absolute Galois group of the actual completion of `F` at `w`, and
`IsGeometricFrobeniusLift`.

Throughout, `w : Global.FinitePlace F` and
`j k : ClosureEmbedding (NumberField.FinitePlace.embedding w)`.

## The shrinking-level cohomology

- `cmSmallLevelDecompositionCohomologyFunctor ... R w d j` is
  `cmSmallLevelGaloisCohomologyFunctor ... R d` followed by
  `DecompositionGroupAction.atFinitePlace _ w j`. It is a functor from
  `ModuleSheaf base R` to
  `Action (SmoothRep R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) (LocalGroup w)`.
- `cmSmallLevelDecompositionCohomologyFunctor_obj_V` and
  `cmSmallLevelDecompositionCohomologyFunctor_ρ`: the underlying smooth
  representation is unchanged, and `g : LocalGroup w` acts as
  `localRestriction w j g` does in the Galois cohomology, by `rfl`.
- `cmSmallLevelDecompositionChangeIso ... R w d j k` is the natural
  isomorphism from the functor for `k` to the functor for `j`, obtained by
  whiskering `atFinitePlaceChangeIso`. Its component at `M` acts by
  `localClosureChange w j k` (`cmSmallLevelDecompositionChangeIso_hom_app_hom`).
- `cmSmallLevelDecompositionCohomology_commutes`: the action of every
  `g : LocalGroup w` commutes with the action of every element of
  `D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`, since it is a morphism of
  smooth representations.

## The prime-to-`m` cohomology

- `cmPrimeToDecompositionCohomologyFunctor ... R m hm K₀ w d j` is
  `cmPrimeToGaloisCohomologyFunctor ... R d` followed by
  `atFinitePlace _ w j`, with values in
  `Action (SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) (LocalGroup w)`.
- `cmPrimeToDecompositionCohomologyFunctor_obj_V` and
  `cmPrimeToDecompositionCohomologyFunctor_ρ` describe it by `rfl` as above.
- `cmPrimeToDecompositionChangeIso ... d j k` is the change-of-embedding
  isomorphism. Its component at `M` acts by `localClosureChange w j k`
  (`cmPrimeToDecompositionChangeIso_hom_app_hom`).
- `cmPrimeToDecompositionCohomology_commutes`: the action of every
  `g : LocalGroup w` commutes with the action of
  `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`.
- `cmPrimeToDecompositionCohomologyComparison_apply ... d j M g x`: the
  comparison
  `cmPrimeToCohomologyComparison ... R (cmSmallLevelArithmeticCoefficients ... R M) d`
  sends the action of `g` on `x` in the prime-to-`m` functor to the action
  of `g` in `cmSmallLevelDecompositionCohomologyFunctor`. It is the
  published `cmPrimeToGaloisCohomologyComparison_apply` at
  `localRestriction w j g`.

## Hecke modules and Frobenius

Let `K'` be a level of `(D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`.

- `cmPrimeToDecompositionHeckeModuleFunctor ... K' d j` is
  `cmPrimeToGaloisHeckeModuleFunctor ... R K' d` followed by
  `atFinitePlace _ w j`, with values in
  `Action (ModuleCat (LevelHecke.LevelHeckeAlgebra R K'.subgroup)) (LocalGroup w)`:
  the `K'`-fixed vectors of the prime-to-`m` cohomology as modules over the
  Hecke algebra of `K'`, with the action of `LocalGroup w`.
- `cmPrimeToDecompositionHeckeModuleIso ... d j`: this functor is isomorphic
  to `cmPrimeToDecompositionCohomologyFunctor ... d j` followed by
  `LevelHecke.heckeModuleActionFunctor R (LocalGroup w) K'.subgroup`. Taking
  fixed vectors commutes with restricting the action; the isomorphism is
  `mapActionResIso` for `LevelHecke.heckeModuleFunctor`, between
  associators.
- `cmPrimeToDecompositionHeckeModule_ρ_smul`: the action of every
  `g : LocalGroup w` commutes with every
  `a : LevelHecke.LevelHeckeAlgebra R K'.subgroup`, since it is a module map.
- `cmPrimeToHeckeFrobenius ... d M j` is
  `DecompositionGroupAction.geometricFrobenius` of the Hecke module
  `(cmPrimeToGaloisHeckeModuleFunctor ... R K' d).obj M` along `j`: the
  endomorphism by which the chosen geometric Frobenius lift at `w` acts.
- `cmPrimeToHeckeFrobenius_smul`: it commutes with every element of the
  Hecke algebra of `K'`.
- `cmPrimeToHeckeFrobenius_eq_of_lift ... hM hg`: if that Hecke module is
  `IsUnramifiedAlong` at `w` and `j`, and `g` satisfies
  `IsGeometricFrobeniusLift w g`, then `g` acts by `cmPrimeToHeckeFrobenius`.
- `cmPrimeToHeckeFrobenius_naturality ... α j`: a morphism `α : M ⟶ N` of
  module sheaves on `Spec F` intertwines the Frobenius endomorphisms through
  the induced Hecke-module map.
- `cmPrimeToHeckeFrobenius_conj ... j k`: the Frobenius endomorphisms along
  `k` and `j` are conjugate by the action of `localClosureChange w j k`.

## Proof outline

Every functor is a published Galois-action functor followed by
`DecompositionGroupAction.atFinitePlace`. The change isomorphisms are
whiskerings of `atFinitePlaceChangeIso`. The commutation results are the
intertwining property of morphisms of smooth representations or module
maps, the published comparison result evaluated at `localRestriction w j g`,
and the generic Frobenius results of `DecompositionGroupAction`.

## Provenance

This is an internal specialization of the generic decomposition group
restriction of `Langlands.Shimura.DecompositionGroupAction` to the published
Galois actions on the cohomology of the actual geometric CM tower. No
action, comparison or Frobenius element is supplied as input. Harris
(1999), Theorem 5.7 and formula (5.6) on printed p. 313, is motivation only.
