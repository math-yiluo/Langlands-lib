# Units of a finite Galois extension of local fields as a Galois module

`Langlands/GaloisCohomology/Local/EulerCharacteristic/Units.lean`, namespace `Langlands.GaloisCohomology.Local`.

For a finite Galois extension `F/E` of nonarchimedean local fields, `G = Gal(F/E)`, a prime `l`
invertible in `E` with `|𝒪[E]/l| = lⁿ`, and an additive function `d` (`Additive.lean`),
`g(Fˣ) = d(ℤ/l) + n · d(𝔽_l[G])` (`g_units_eq`). The units are compared with the valuation
(`Fˣ/𝒪[F]ˣ ≅ ℤ`, the Library's normalized order), `𝒪[F]ˣ` with a deep unit group `U^k` (finite
index), `U^k/(U^k)^l` with `𝓂^k/l𝓂^k` (`unitToModN`, by the binomial expansion of `(1 + x)^l`;
no logarithm), and `𝓂^k` with a lattice spanned by a normal basis, which is free over `𝒪[E][G]`.
The file also contains the units part of the vanishing argument: inertia acting through a
coprime order acts trivially on `Fˣ/Fˣˡ` (`exists_map_units_eq_mul_pow`).

## Declarations

- Powers of principal units: `one_add_pow_prime_eq`, `one_add_pow_sub_one_eq`,
  `pow_mem_unitFiltration`, `pow_mem_unitFiltration_succ_iff`,
  `eq_one_of_mem_unitFiltration_of_pow_eq_one`.
- Galois actions: `coe_integer_smul`, `coe_integerUnits_smul`, `smul_mem_maximalIdeal`,
  `smul_mem_maximalIdeal_pow`, `smul_mem_unitFiltration`, `unitFiltrationAction`, `maxPow F k`
  (`𝓂^k` as an additive group), `maxPowAction`.
- `mem_maximalIdeal_pow_add_iff`, `unitToModN : U^k → 𝓂^k/l𝓂^k`, `unitToModN_surjective`,
  `unitToModN_eq_zero_iff` (kernel `(U^k)^l` for `k ≥ e + 1`), `unitToModN_smul`.
- Normal lattices: `normalSub E θ`, `normalSubAction`, `normalSubOfCoeff`, `normalSubEquiv`
  (`𝒪[E]^G ≅ normalSub`), `smul_normalSubOfCoeff`; `coeffToRegular` (to `(𝔽_l[G])ⁿ`),
  `coeffToRegular_eq_zero_iff`, `coeffToRegular_surjective`, `coeffToRegular_perm`.
- `modNEquivOfSurjective`, `modNEquivOfSurjective_apply_modNRep`; `trivialIntAction`,
  `finite_modN_uliftInt`, `finite_torsN_uliftInt`.
- `ordHom F : Fˣ → ℤ` (the Library's `normalizedUnitOrder`), `ordHom_surjective`, `ordHom_exact`,
  `discreteLocalValuation_algEquiv_apply`, `ordHom_smul`, `integerUnitsMap_toAdditive_smul`.
- `finite_quotient_range_toAdditive`, `finite_modN_of_finite_cokernel`,
  `finite_torsN_of_torsion_trivial`, `integer_subgroup_torsion`, `modNIntegerEquiv`,
  `finrank_modN_integer`, `exists_card_quotient_eq_pow`, `finite_modN_maxPow`,
  `finite_torsN_integerUnits`, `exists_maxPow_le_normalSub`, `finite_quotient_maxPow`.
- `g_units_eq_one_add`, `g_integerUnits_eq`, `g_units_eq`.
- `mul_inv_mem_of_iterate_eq`, `exists_map_units_eq_mul_pow`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsPower.lean`, `UnitsLattice.lean`,
`ModNEquivOfSurjectiveApplyModNRep.lean` and `VanishingUnits.lean`. Mechanical renames (as in the foundations, `Langlands/Cohomology/Profinite/`): `IsDiscreteRep` → `IsSmoothRep`, `cohomologyMap` → `coeffMap`, `cohomologyMapAlong φ hφ` → `map ⟨φ, hφ⟩`, `cochainsComplex` → `cochains`, `cohomologyRes/Cores/ResLE` → `res/cores/resOfLE`, `H0Iso` → `zeroIso`, `eulerChar` → `eulerCharacteristic` (also inside names), `galUnits`/`galRootsOfUnity` → `unitsModule`/`rootsOfUnityModule` (lemma names keep `galUnits`/`galRootsOfUnity`), `unitsIncl` → `integerUnitsMap`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Changes: the source's `ordHom` (on its own `ord`) is the Library's `normalizedUnitOrder` with values
in `ULift ℤ`; `ord_algEquiv` is replaced by `discreteLocalValuation_algEquiv_apply`. The source's
`integerAction` here is that of `Arithmetic/Ramification.lean`, and its global instance
`integerUnitsAction` is a local instance. The two root-extraction theorems of `UnitsPower.lean` are
in `Arithmetic/Units.lean`.

## References

- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm, 1962), 288–295, §2, Theorem 2.2 and the sketch of its proof, p. 289
  (the local Euler characteristic formula, for `k` complete under a discrete valuation with finite
  residue field and `|M|` invertible in `k`, §1, p. 288).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §3, Theorem
  (7.3.1) and its proof, pp. 392–396.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.7, Theorem 5 and its proof (for `p`-adic fields),
  pp. 99–101.
- J.-P. Serre, *Local Fields*, chapter IV, §2, Proposition 6 (the unit filtration), p. 66; J.-P.
  Serre, *Galois Cohomology*, chapter II, §5.7, proof of Lemma 5 (units and the normal basis
  theorem, for `p`-adic fields), pp. 100–101.
