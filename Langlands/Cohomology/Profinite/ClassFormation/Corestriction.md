# Corestriction in a class formation

`Langlands/Cohomology/Profinite/ClassFormation/Corestriction.lean`, namespace
`Langlands.ProfiniteCohomology`.

For open subgroups `V ≤ U` of a compact group, corestriction `Hⁿ(V, C) → Hⁿ(U, C)` composed with
restriction is multiplication by `[U : V]`. In a class formation, corestriction on `H²`
preserves invariants: `inv_U(cor x) = inv_V(x)`, and restriction on `H²` is surjective.

## Declarations

- `resSubgroupOfInvHom`, `map_resSubgroupOfHom_comp`: the inverse of the identification of
  `H*(V, ·)` with `H*(V ∩ U, ·)` (as a subgroup of `U`).
- `openSubgroupOf U V`: `V` as an open subgroup of `U`.
- `coresOfLE C h n : Hⁿ(V, C) → Hⁿ(U, C)` for open `V ≤ U` (`coresOfLE_eq`: the identification
  followed by the corestriction `cores` of `Corestriction.lean` for the open subgroup
  `V ∩ U` of `U`).
- `resOfLE_comp_coresOfLE`, `coresOfLE_resOfLE`: `cor ∘ res = [U : V]`.
- `QZ.exists_nsmul_eq`: `ℚ/ℤ` is divisible.
- `PreClassFormation.inv_coresOfLE_resOfLE`, `PreClassFormation.resOfLE_eq_of_inv`,
  `PreClassFormation.inv_coresOfLE_of`: invariants of corestrictions of restrictions, and of
  corestrictions of classes in the image of restriction.
- `ClassFormation.resOfLE_surjective` (restriction on `H²` is surjective) and
  `ClassFormation.inv_coresOfLE` (`inv_U ∘ cor = inv_V`).
- `quotOpenSubgroup`, instance `compactSpace_quotientGroup` (a quotient of a compact group is
  compact).
- `ClassFormation.At.inv_coresOfLE`: the same for a class formation for a set of primes `P`, for
  classes killed by an integer prime to the complement of `P`, when `[U : V]` involves only
  primes of `P`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/ClassFormations/CorestrictionDefs.lean` and
`src/GroundTheory/ProfiniteCohomology/ClassFormations/Corestriction.lean`. The repository has no
licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names: `cohomologyCoresLE` → `coresOfLE`,
`cohomologyResLE` → `resOfLE`, `cohomologyCores` → `cores` (and accordingly
`cohomologyResLE_comp_cohomologyCoresLE` → `resOfLE_comp_coresOfLE`, …), `ClassFormationAt` →
`ClassFormation.At`; the other names are the source's.

## References

- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter XI,
  §2, Proposition 1, p. 167 (restriction on `H²` is surjective; corestriction is injective and
  `inv_E ∘ Cor = inv_E'`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §1, Remark 2 to Definition (3.1.8), p. 156 (corestriction
  and invariants).
