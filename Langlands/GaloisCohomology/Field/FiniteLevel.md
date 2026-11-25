# Finite levels: inflation from finite Galois subextensions

`Langlands/GaloisCohomology/Field/FiniteLevel.lean`, namespace `Langlands.GaloisCohomology`.

For a Galois extension `L/K` and a finite Galois subextension `E`, inflation along
`Gal(L/K) → Gal(E/K)` and `Eˣ → Lˣ` maps `Hⁿ(Gal(E/K), Eˣ)` (Mathlib's `groupCohomology` of the
finite group) to `Hⁿ(Gal(L/K), Lˣ)`. Every class comes from some finite level, and in degree `2`
inflation is injective (because of Hilbert 90 for the intermediate extensions). In degree `2`
the target is the cohomological Brauer group `H²(Gal(L/K), Lˣ)`, and these statements say that
it is the union of the relative Brauer groups `H²(Gal(E/K), Eˣ)`.

## Declarations

- `galoisBrauerGroup K L`: `H²(Gal(L/K), Lˣ)` in the cochain model; `cohomologicalBrauerGroup K Ksep`
  the same for a separable closure.
- `unitsRestrictHom E`: the inclusion `Eˣ → Lˣ` as a morphism from the restriction along
  `Gal(L/K) → Gal(E/K)` (`unitsRestrictHom_hom_apply`); `isLocallyConstant_unitsInflation`,
  `unitsInflationCochainsX`, `unitsInflationCochains E` (the inflation of cochains, with
  `unitsInflationCochainsX_comp_ι`, `unitsInflationCochains_comp_cochainsι`,
  `unitsInflationCochains_f_hom_apply`), and `unitsInflation E n : Hⁿ(Gal(E/K), Eˣ) →
  Hⁿ(Gal(L/K), Lˣ)`; `brauerInflation E` in degree `2`.
- `quotientEquivGal_mk_eq_restrictNormalHom`, `inflation_unitsModule_eq`: the inflation from the
  finite quotient `Gal(L/K)/U` is `unitsInflation` for the fixed field `L^U`.
- `exists_unitsInflation_eq`, `exists_brauerInflation_eq`: every class of `Hⁿ(Gal(L/K), Lˣ)` is
  inflated from a finite Galois subextension.
- Towers `K ⊆ E ⊆ F`: `unitsTowerHom`, `unitsInflationTower`; for subextensions `E ≤ F` of `L`:
  `galRestrictOfLE`, `unitsOfLE`, `unitsInflationOfLE` (with their `_apply` lemmas).
- `map_two_injective_of_surjective`: for a surjection `Q → P` of groups and a module `A` of `Q`
  whose `ker`-invariants are `B`, with `H¹(ker, A) = 0`, the map `H²(P, B) → H²(Q, A)` is
  injective. The proof uses the Library's inflation–restriction theorem in degree two
  (`Langlands.Cohomology.h2InflationRestrictionExactness`, for Mathlib's `HInfRes`).
- `galTowerKerHom`, `galTowerKerEquiv` (`coe_galTowerKerEquiv_apply`): `Gal(F/E)` is the kernel of
  `Gal(F/K) → Gal(E/K)`; `isZero_groupCohomology_one_ker_unitsModule`, `unitsTowerHom_injective`,
  `exists_unitsTowerHom_eq`, `unitsInflationTower_two_injective`,
  `unitsInflationOfLE_two_injective`: inflation on `H²` between finite levels is injective.
- `galRestrictOfLE_restrictNormalHom`, `cochainsMap_galRestrictOfLE_comp_unitsInflationCochains`,
  `unitsInflationOfLE_comp_unitsInflation`: compatibility of the inflations;
  `fixedField_le_of_le`, `transition_comp_groupCohomologyQuotientUnitsModuleIso`.
- `unitsInflation_fixedField_two_injective`, `unitsInflation_two_injective_of_eq`,
  `brauerInflation_injective`: inflation from a finite Galois level to `H²(Gal(L/K), Lˣ)` is
  injective.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean`
(sections "Brauer" and "Inflation"), `.../GaloisCohomology/Brauer.lean`,
`.../GaloisCohomology/BrauerInflationDefs.lean` and `.../GaloisCohomology/BrauerInflation.lean`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Names are the source's, with `galUnits` → `unitsModule`. Notions replaced: the source's
inflation–restriction for finite groups (`GroundTheory.GroupCoh.inflation`,
`inflation_two_injective`, from its own Tate cohomology files) by Mathlib's `HInfRes` and the
Library's `h2InflationRestrictionExactness`; the source's transition maps of the finite-quotient
system by the Library's `Langlands.Continuous.finiteInflation` and `quotientTransition` (through
`ProfiniteCohomology.transition`).

## References

- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter X, §4,
  Proposition 6, its Corollary and Remark 1, p. 156 (`H²(/k)` is the direct limit, and in fact the
  union, of the `H²(K/k)`), and §5, p. 157 (the same for the classical Brauer group).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VI, §3, p. 350 (`Br(K) = ⋃ Br(L|K)`), and Theorem (6.3.4) with
  the inflation diagram before it, p. 351.
