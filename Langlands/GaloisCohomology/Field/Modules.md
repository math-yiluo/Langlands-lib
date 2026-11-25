# Galois modules of a field extension

`Langlands/GaloisCohomology/Field/Modules.lean`, namespace `Langlands.GaloisCohomology`.

For an extension `L/K`, the Galois group `Gal(L/K)` acts on `L`, on `Lˣ` and on the roots of
unity `μ_n(L)`. This file makes these actions into representations — the coefficient modules of
Galois cohomology — and shows that they are smooth when `L/K` is algebraic, so that the
cohomology of `Langlands.ProfiniteCohomology` applies to them.

## Declarations

Representations from actions by endomorphisms.

- `intRep φ`: a monoid action by additive endomorphisms as a representation over `ULift ℤ`
  (`intRep_apply`); `intRepOfMonoidEnd φ`, `zRepOfMonoidEnd φ`: an action by endomorphisms of a
  commutative group `M`, on `Additive M`, over `ULift ℤ` and over `ℤ`
  (`intRepOfMonoidEnd_apply`, `zRepOfMonoidEnd_apply`).
- `uliftIntLinearMap f`, `uliftIntLinearEquiv e`: an additive map (equivalence) as a
  `ULift ℤ`-linear one (`uliftIntLinearMap_apply`, `uliftIntLinearEquiv_apply`).

The modules.

- `galUnitsHom K L`, `galRootsOfUnityHom K L n`: the actions of `Gal(L/K)` on `Lˣ` and on
  `μ_n(L)` (`coe_galUnitsHom_apply`, `coe_galRootsOfUnityHom_apply`).
- `additiveModule K L`: `L` with the Galois action, a representation over `K`.
- `unitsModule K L`: `Lˣ` (written additively) with the Galois action, over `ULift ℤ`; it *is* the
  Library's `Langlands.ClassFieldTheory.Local.unitsRepresentation K L` (an abbreviation).
- `rootsOfUnityModule K L n`: `μ_n(L)` (written additively) with the Galois action, over
  `ULift ℤ`.
- `unitsModuleZ K L`, `rootsOfUnityModuleZ K L n`: the same modules over the integers `ℤ` (used
  by the cup product with characters, whose classes live in `H²(G, ℤ)` over `ℤ`).
- `additiveModule_ρ_apply`, `unitsModule_ρ_apply`, `coe_unitsModule_ρ_apply`,
  `unitsModuleZ_ρ_apply`, `rootsOfUnityModule_ρ_apply`, `rootsOfUnityModuleZ_ρ_apply`: the
  actions on elements.
- `rootsOfUnityToUnits K L n : μ_n(L) → Lˣ`, the inclusion as a morphism of Galois modules
  (`rootsOfUnityToUnits_hom_apply`).

Topology and smoothness.

- `galois_compactSpace`, `galois_t2Space`, `galois_isProfinite`: the Galois group of a Galois
  extension is profinite.
- `apply_eq_of_mem_fixingSubgroup_adjoin`; `isOpen_of_forall_apply_eq_mem`: for an algebraic
  extension, a subgroup containing the stabilizer of an element of `L` is open.
- Instances `isSmoothRep_additiveModule`, `isSmoothRep_unitsModule` (through the Library's open
  stabilizer `unitOpenStabilizer`), `isSmoothRep_unitsModuleZ`, `isSmoothRep_rootsOfUnityModule`,
  `isSmoothRep_rootsOfUnityModuleZ`, for an algebraic extension.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean`,
`src/GroundTheory/ProfiniteCohomology/GaloisModules/Discrete.lean`, with `uliftIntLinearMap` and
`rootsOfUnityToUnits` from `src/GroundTheory/ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean`
and `uliftIntLinearEquiv` from
`src/GroundTheory/ProfiniteCohomology/GaloisCohomology/IsZeroGroupCohomologyQuotientToInvariantsGalAdd.lean`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Names and notions replaced: `galUnits` → `unitsModule`, defined as the Library's
`unitsRepresentation` (same carrier `Additive Lˣ`, same action; the source's module had a free
universe for `ULift ℤ`, the Library's uses the universe of `L`); `galRootsOfUnity` →
`rootsOfUnityModule`, `galAdd` → `additiveModule`, `galUnitsZ` → `unitsModuleZ`,
`galRootsOfUnityZ` → `rootsOfUnityModuleZ`, and accordingly in lemma names
(`isDiscreteRep_galUnits` → `isSmoothRep_unitsModule`, …). The source's `galAddInt` and
`galAddZ` (the additive module over `ULift ℤ` and over `ℤ`) are not taken: nothing in the
source uses them.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter II, §1.1, p. 71 (Galois cohomology: discrete
  `Gal(K/k)`-modules).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VI, §1, p. 337 (Galois groups as profinite groups; the additive
  group as a Galois module).
