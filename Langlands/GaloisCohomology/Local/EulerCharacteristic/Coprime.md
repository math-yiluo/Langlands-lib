# The Euler characteristic in the coprime case

`Langlands/GaloisCohomology/Local/EulerCharacteristic/Coprime.lean`, namespace `Langlands.GaloisCohomology.Local`.

Let `V ≤ U` be open subgroups of `Gal(Ksep/K)`, `V` normal in `U` of index prime to `l`, with `μ_l`
in the fixed field of `V`, and `M` a finite `l`-torsion module of `U` on which `V` acts trivially.
Then `χ(U, M) = |M|^{-n}` where `|𝒪[E]/l| = lⁿ` for the fixed field `E` of `U`
(`eulerCharacteristic_coprime`). By `Twist.lean` the cohomology of `U` is the `Gal(F/E)`-invariant
part of `Hⁱ(V, μ_l) ⊗ Hom(μ_l, M)`; in degree one `H¹(V, μ_l) ≅ Fˣ/Fˣˡ` (`Kummer.lean`), whose
value under the additive function `X ↦ dim (X ⊗ Hom(μ_l, M))^{Gal(F/E)}` is computed in
`Units.lean`. The vector spaces over `ℤ/l` whose cohomology is taken are over `ULift.{u} (ZMod l)`,
the field `ℤ/l` in the universe `u` of the Galois group (the cohomology of a representation needs
its ring and its group in one universe); the additive functions of `Units.lean` are on
representations over `ZMod l`, which are viewed over `ULift (ZMod l)` by `zmodRepULift`
(`AdditiveFunction.invariantsTensorULift`).

## Declarations

- `natCard_eq_pow_finrank_zmod`, `finrank_eq_of_natCard_zmod` (`|V| = l^{dim V}` over
  `ULift (ZMod l)`), `nsmul_galRootsOfUnity_eq_zero`, `rootsRepZMod l U` (`μ_l` as a representation
  of `U` over `ULift (ZMod l)`), `finrank_rootsRepZMod`, `rootsRepZMod_ρ_of_mem`,
  `rootsCohomologyZModEquiv`, `rootsCohomologyZModEquiv_cohomologyConj`,
  `finite_cohomology_roots_subgroupOf`.
- `ulift_zmod_smul_eq_zsmul`, `addEquivZModLinear` (an additive isomorphism of modules over
  `ULift (ZMod l)` is linear), `zmodRepULift ρ` (a representation over `ZMod l` viewed over
  `ULift (ZMod l)`), `zmodRepULift_apply`, `finrank_invariants_tprod_eq_of_linearEquiv` (the
  dimension of the invariants of `X ⊗ N` depends on `X` up to equivariant isomorphism),
  `finrank_invariants_zmodRepULift_leftRegular_tprod` (`dim (k[Γ] ⊗ N)^Γ = dim N`),
  `AdditiveFunction.invariantsTensorULift` (the additive function
  `X ↦ dim_{ULift (ZMod l)} (X ⊗ N)^Γ`, `|Γ|` prime to `l`), `invariantsTensorULift_apply`,
  `toFun_cohomologyConjRep_eq` (its value on the cohomology of `μ_l` twisted by conjugation, through
  an equivariant additive isomorphism).
- `finrank_cohomology_alternating_sum_coprime`, `finite_cohomology_coprime`,
  `eulerCharacteristic_coprime`, `finite_cohomology_coprime_of_torsion`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Coprime.lean`. Mechanical renames (as in the foundations, `Langlands/Cohomology/Profinite/`): `IsDiscreteRep` → `IsSmoothRep`, `cohomologyMap` → `coeffMap`, `cohomologyMapAlong φ hφ` → `map ⟨φ, hφ⟩`, `cochainsComplex` → `cochains`, `cohomologyRes/Cores/ResLE` → `res/cores/resOfLE`, `H0Iso` → `zeroIso`, `eulerChar` → `eulerCharacteristic` (also inside names), `galUnits`/`galRootsOfUnity` → `unitsModule`/`rootsOfUnityModule` (lemma names keep `galUnits`/`galRootsOfUnity`), `unitsIncl` → `integerUnitsMap`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Two declarations raise `maxHeartbeats` to
`400000`, as in the source, with a comment.

## References

- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm, 1962), 288–295, §2, Theorem 2.2 and the sketch of its proof, p. 289
  (the local Euler characteristic formula, for `k` complete under a discrete valuation with finite
  residue field and `|M|` invertible in `k`, §1, p. 288).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §3, Theorem
  (7.3.1) and its proof, pp. 392–396.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.7, Theorem 5 and its proof (for `p`-adic fields),
  pp. 99–101.
