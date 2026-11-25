# Fundamental classes of a class formation

`Langlands/Cohomology/Profinite/ClassFormation/FundamentalClass.lean`, namespace
`Langlands.ProfiniteCohomology`.

Let `C` be a class formation over a compact group `G`, `U` an open subgroup and `V ⊆ U` an open
subgroup normal in `U`. Then `H¹(V, C) = 0` makes inflation `H²(U/V, C^V) → H²(U, C)` injective,
with image the classes vanishing on `V`, so there is a unique class `u_{U/V}` (the fundamental
class) whose inflation has invariant `1/[U : V]`. Its restrictions to the subgroups `S` of the
finite group `U/V` generate `H²(S, C^V)`, which is cyclic of order `|S|`, and `H¹(S, C^V) = 0`:
these are exactly the hypotheses of Tate's theorem for the finite group `U/V` and the module
`C^V`. The same holds for a class formation for a set of primes `P`, when `[U : V]` involves
only primes of `P`.

## Declarations

Subgroups of `U ⧸ V` and their preimages.

- `QZ.mem_of_nsmul_eq_zero`: a subgroup of `ℚ/ℤ` containing the `p`-primary parts for `p ∈ P`
  contains every element killed by an integer whose prime factors lie in `P`.
- `quotPreimage U V S`: the preimage in `U` of a subgroup `S` of `U ⧸ V`
  (`quotPreimage_le`, `mem_quotPreimage`, `le_quotPreimage`); `quotPreimageHom S` (to `S`,
  surjective with kernel `V`: `coe_quotPreimageHom_apply`, `quotPreimageHom_surjective`,
  `quotPreimageHom_eq_one_iff`, `quotPreimageHom_ker`), `normal_subgroupOf_quotPreimage`,
  `quotPreimageEquiv S : quotPreimage S ⧸ V ≃* S`, `relIndex_quotPreimage` (`[quotPreimage S : V] = |S|`).
- Topology: `continuous_quotPreimageHom`, `continuous_quotPreimageEquiv`, `isOpen_subgroupOf`,
  `discreteTopology_quot` (`U ⧸ V` is discrete for `V` open), `continuous_quotPreimageEquiv_symm`;
  instance `isSmoothRep_res_quotientToInvariants_res`.
- `quotPreimageRepHom`, `inflQuot C S n : Hⁿ(S, C^V) → Hⁿ(quotPreimage S, C)` (inflation through
  the preimage), `res_comp_inflQuot`, `quotPreimageInvHom`, `quotPreimageInvHom_bijective`,
  `inflQuot_eq` (it is an isomorphism followed by the inflation for `quotPreimage S`),
  `isIso_map_quotPreimageEquiv`.

Inflation in degree two.

- `QZ.cyclic_of_injective`: an element whose image under injective maps to `ℚ/ℤ` is `1/n`, in a
  group killed by `n`, has order `n` and generates. `QZ.nsmul_mk_one_div_mul`.
- `compactSpace_of_isOpen`, `isZero_H1_subgroupOf`, `infl_two_injective_of_open` (inflation is
  injective on `H²` when `H¹(V, A) = 0`), `mem_range_infl_two_iff` (its image is the kernel of
  restriction to `V`), `relIndex_ne_zero_of_isOpen`.
- `quotPreimageOpen hVU S`: `quotPreimage S` as an open subgroup, with the normality instance.

Fundamental classes.

- `PreClassFormation.mem_range_infl_two_iff`, `PreClassFormation.inv_infl_fundamentalClass`: the
  inflation of `fundamentalClass U V` has invariant `1/[U : V]` (when such a class exists and
  `inv V` is injective).
- `inflQuot_one_injective`, `inflQuot_two_injective`, `resLE_inflQuot`, `inv_inflQuot_res`,
  `inv_inflQuot_res_fundamentalClass`: the restriction of the fundamental class to `S` inflates to
  a class of invariant `1/|S|`.
- `PreClassFormation.cyclic_res_fundamentalClass`: the restriction of the fundamental class to `S`
  has order `|S|` and generates `H²(S, C^V)`.
- `PreClassFormation.groupFundamentalClass U V`: the fundamental class in Mathlib's
  `groupCohomology` of the finite group `U ⧸ V`; `groupCohomology_map_groupFundamentalClass`
  (its restrictions correspond to those of `fundamentalClass` under `toGroupCohomology`).
- `PreClassFormation.tate_hypotheses`, `ClassFormation.tate_hypotheses`,
  `ClassFormation.At.tate_hypotheses`: for every subgroup `S` of `U ⧸ V`, `H¹(S, C^V) = 0`, the
  restriction of the group fundamental class to `S` has order `|S|` and generates `H²(S, C^V)`.
- `ClassFormation.inv_injective`, `ClassFormation.exists_inv_eq`,
  `ClassFormation.At.exists_inv_eq_one_div`.
- `quotQuotHom`, `continuous_quotQuotHom`, `quotQuotRepHom`, `inflQuotQuot`: inflation from
  `U ⧸ V` to `U ⧸ V'` for `V' ≤ V`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/ClassFormations/Quotient.lean`,
`src/GroundTheory/ProfiniteCohomology/ClassFormations/Finite.lean` and
`src/GroundTheory/ProfiniteCohomology/ClassFormations.lean`. The repository has no licence file;
its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's, with `cohomologyInfl`,
`cohomologyRes`, `cohomologyResLE` → `infl`, `res`, `resOfLE`, `ClassFormationAt` →
`ClassFormation.At`, `cohomologyIsoGroupCohomology` → `isoGroupCohomology` (and its forward map
`toGroupCohomology`), and homomorphisms bundled as `H →ₜ* G`.

## References

- E. Artin, J. Tate, *Class Field Theory* (AMS Chelsea 2009, reprint with corrections of the 1967
  edition), chapter XIV, §3, p. 153 (the fundamental class of a layer; Proposition 4 and Corollary
  1: its restrictions are the fundamental classes of the sublayers and generate their `H²`), and §4,
  Theorem 1, p. 154.
- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter XI,
  §3, p. 168 (the fundamental classes `u_{F/E}` and their properties; they satisfy the hypotheses of
  Theorem 14 of chapter IX, §8).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §1, Definition (3.1.3), p. 149 (class modules, fundamental
  classes), and Remark 5 to Definition (3.1.8), p. 157 (the modules `C^U` are class modules, with
  compatible fundamental classes).
