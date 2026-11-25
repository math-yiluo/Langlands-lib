# Additive Hilbert 90

`Langlands/GaloisCohomology/Field/AdditiveHilbert90.lean`, namespace `Langlands.GaloisCohomology`.

For a Galois extension `L/K`, `Hⁿ(Gal(L/K), L) = 0` for all `n ≥ 1`. For a finite extension
this follows from the normal basis theorem: `L` is the coinduced module of `K` from the trivial
subgroup, hence acyclic. For an infinite extension one passes to the limit over the finite
quotients `Gal(L/K)/U`, using that the `U`-invariants of `L` are the finite Galois extension
`L^U`.

## Declarations

Finite extensions (Mathlib's `groupCohomology`).

- `normalBasis_repr_apply_smul`: the Galois action on coordinates in a normal basis.
- `galoisCoindIso k K L`: `L` with the Galois action is isomorphic to the module coinduced from
  the trivial subgroup by `K` (over any coefficient ring `k`).
- `isZero_groupCohomology_succ`, `isZero_groupCohomology`, `isZero_groupCohomology_galois`,
  `subsingleton_groupCohomology_galois`: `Hⁿ(Gal(L/K), L) = 0` for `n ≥ 1` and `L/K` finite
  Galois; `isCoboundary₁_of_isCocycle₁_galois`: every `1`-cocycle `Gal(L/K) → L` is a coboundary.

Profinite groups.

- `isZero_cohomology_of_forall_isZero`: for a profinite group, if the cohomology in degree `n` of
  the `U`-invariants as a module of `G/U` vanishes for every open normal `U`, so does `Hⁿ(G, A)`
  (passage to the limit through `exists_inflation_eq`).

Galois extensions.

- `groupCohomologyQuotientAdditiveModuleIso U n`: the cohomology of `Gal(L/K)/U` with values in
  `L^U` is that of `Gal(L^U/K)`;
  `isZero_groupCohomology_quotientToInvariants_additiveModule`.
- `isZero_cohomology_additiveModule`, `subsingleton_cohomology_additiveModule`:
  `Hⁿ(Gal(L/K), L) = 0` for `n ≥ 1` and any Galois extension `L/K`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/AdditiveHilbert.lean` and the sections "Profinite" and
"Additive" of
`src/GroundTheory/ProfiniteCohomology/GaloisCohomology/IsZeroGroupCohomologyQuotientToInvariantsGalAdd.lean`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's, with `galAdd`
→ `additiveModule` (`isZero_cohomology_galAdd` → `isZero_cohomology_additiveModule`, …).

## References

- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter X, §1,
  Proposition 1, p. 150 (`Ĥⁿ(G, K) = 0` for a finite Galois extension, by the normal basis theorem).
  Serre states it for a finite Galois extension.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VI, §1, Proposition (6.1.1), p. 337 (for an arbitrary Galois
  extension).
