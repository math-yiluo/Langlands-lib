# Hilbert's theorem 90

`Langlands/GaloisCohomology/Field/Hilbert90.lean`, namespace `Langlands.GaloisCohomology`.

For a Galois extension `L/K`, `H¹(Gal(L/K), Lˣ) = 0`, for the units module `unitsModule K L` (the
Library's `unitsRepresentation`) in the cochain model of `Langlands.ProfiniteCohomology`. For a
finite extension this is Mathlib's Hilbert 90 for `groupCohomology`; for an infinite extension
one passes to the limit over the finite quotients.

## Declarations

- `mem_fixedField_of_mem_invariants_unitsModule`, `invariantsUnitsModuleAddEquiv H`: the units
  fixed by a subgroup `H` are the units of the fixed field `L^H`
  (`coe_invariantsUnitsModuleAddEquiv_apply`); `invariantsUnitsModuleAddEquiv_quotientToInvariants`:
  compatibility with the actions of `Gal(L/K)/U` and `Gal(L^U/K)`.
- `invariantsUnitsModuleLinearEquiv U` (`invariantsUnitsModuleLinearEquiv_apply`) and
  `groupCohomologyQuotientUnitsModuleIso U n`: the cohomology of `Gal(L/K)/U` with values in the
  `U`-invariant units is that of `Gal(L^U/K)` with values in `(L^U)ˣ`.
- `isZero_groupCohomology_one_unitsModule K E`: Hilbert 90 for a finite extension `E/K`, in
  Mathlib's `groupCohomology` (from Mathlib's
  `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`).
- `isZero_groupCohomology_one_quotientToInvariants_unitsModule`,
  `isZero_cohomology_one_unitsModule`, and `subsingleton_cohomology_one_unitsModule`:
  `H¹(Gal(L/K), Lˣ) = 0` for every Galois extension `L/K`.

The Library proves Hilbert 90 for the absolute Galois group of a field in Mathlib's continuous
cohomology (`Langlands.ClassFieldTheory.Local.absoluteH1Vanishing`, for `AlgebraicClosure K`);
the statement here is for every Galois extension, in the cochain model. The two agree through
`isoContinuousCohomology`.

## Source and licence

Ported from the sections "Units" and "Hilbert90" of
`src/GroundTheory/ProfiniteCohomology/GaloisCohomology/IsZeroGroupCohomologyQuotientToInvariantsGalAdd.lean`
of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's, with `galUnits` →
`unitsModule` (`subsingleton_cohomology_one_galUnits` → `subsingleton_cohomology_one_unitsModule`,
…). `invariantsUnitsModuleLinearEquiv` is new: it states the linear
equivalence with the module structures of the two representations, which the Library's
`unitsRepresentation` (a definition, not an abbreviation) requires for rewriting.

## References

- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter X, §1,
  Proposition 2, p. 150 (`H¹(G, K*) = 0`), with Remark 1, p. 151 (Hilbert's theorem 90). Serre
  states it for a finite Galois extension.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VI, §2, Theorem (6.2.1), p. 344 (for an arbitrary Galois
  extension).
