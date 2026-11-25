# Additive functions on finite modular representations

`Langlands/GaloisCohomology/Local/EulerCharacteristic/Additive.lean`, namespace `Langlands.GaloisCohomology.Local` (with the sub-namespace `AdditiveFunction`).

The computation of the local Euler characteristic in the coprime case reduces to evaluating an
*additive function* `d` on finite `𝔽_l[Γ]`-modules (a function additive on short exact sequences)
on the `l`-torsion and `l`-cotorsion of infinite groups like `Fˣ`. For an abelian group `A` with an
action of a finite group `Γ` such that `A/lA` and `A[l]` are finite, `d.g A = d(A/lA) − d(A[l])`.
The file sets up `A/lA` (`ModN`), `A[l]` (`TorsN`), their representations, the snake lemma for
`0 → A → B → C → 0` (`connecting`), and proves `g` additive, invariant under finite cokernels and
torsion-free changes, and its value on `ℤ` with trivial action.

## Declarations

- `TorsN A n` (`A[n]`), `mem_ker_lsmul_iff`, instance `TorsN.instModule`; instance
  `additiveDistribMulAction` (an action on `M` gives one on `Additive M`).
- `piRep ι ρ`, `intRepToZMod`, `modNRep Γ A n`, `torsNRep Γ A n` (the representations on `A/nA` and
  `A[n]`).
- `structure AdditiveFunction l Γ` (`toFun` on finite `ℤ/l`-representations, additive on short exact
  sequences); `g`, `g_eq`, `g_of_not_finite`, `one` (the value on the trivial module `ℤ/l`).
- Invariants: `mapsTo_invariants`, `exists_invariant_preimage`, `finrank_invariants_additive`,
  `invariantsTensor l Γ` (the additive function `X ↦ dim (X ⊗ T)^Γ` for a module `T`).
- `finite_of_exact`, `toFun_congr`, `toFun_eq_ker_add_range`, `toFun_subrep_congr`,
  `toFun_range_of_injective`, `toFun_range_of_surjective`, `alternating_sum_six`.
- The snake sequence: `torsNMap`, `modNMap`, `connecting`, `exact_torsNMap_torsNMap`,
  `exact_torsNMap_connecting`, `exact_connecting_modNMap`, `exact_modNMap_modNMap`, intertwining
  lemmas; `finite_torsN_of_exact`, `finite_modN_of_exact`, `finite_torsN_of_injective`,
  `finite_modN_of_surjective`.
- `subgroupDistribMulAction`, `quotientDistribMulAction`.
- `g_add`: `g` is additive on short exact sequences; `toFun_prod`, `toFun_pi`,
  `g_eq_of_torsion_trivial`, `g_eq_zero_of_nsmul_eq_zero`, `g_eq_zero_of_finite`,
  `g_eq_of_finite_cokernel`, `g_of_trivial_int`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveDefs.lean`, `AdditiveInvariants.lean`, `AdditiveSnake.lean`
and `Additive.lean`. Mechanical renames (as in the foundations, `Langlands/Cohomology/Profinite/`): `IsDiscreteRep` → `IsSmoothRep`, `cohomologyMap` → `coeffMap`, `cohomologyMapAlong φ hφ` → `map ⟨φ, hφ⟩`, `cochainsComplex` → `cochains`, `cohomologyRes/Cores/ResLE` → `res/cores/resOfLE`, `H0Iso` → `zeroIso`, `eulerChar` → `eulerCharacteristic` (also inside names), `galUnits`/`galRootsOfUnity` → `unitsModule`/`rootsOfUnityModule` (lemma names keep `galUnits`/`galRootsOfUnity`), `unitsIncl` → `integerUnitsMap`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

## References

- J.-P. Serre, *Local Fields*, chapter VIII, §4 (the Herbrand quotient, p. 133, and its
  multiplicativity, Propositions 7 and 8 and Corollary, p. 134, the model for the additive functions
  here), pp. 132–134.
- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm, 1962), 288–295, §2, Theorem 2.2 and the sketch of its proof, p. 289
  (the local Euler characteristic formula, for `k` complete under a discrete valuation with finite
  residue field and `|M|` invertible in `k`, §1, p. 288).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §3, Theorem
  (7.3.1) and its proof, pp. 392–396.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.7, Theorem 5 and its proof (for `p`-adic fields),
  pp. 99–101.
