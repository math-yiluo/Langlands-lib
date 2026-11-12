# Reduction of cocenter generation to kernel generation

Authors: Worker 183.

The module `Langlands.GroupScheme.SimplyConnected.RankOneLeviCocenterGenerationReduction` proves

```
theorem rankOneLeviCocenterGeneration_of_leviCocenterKernelGeneration
    (hker : LeviCocenterKernelGenerationStatement.{u}) :
    RankOneLeviCocenterGenerationStatement.{u}
```

That is, kernel generation of the cocenter of the minimal Levi subgroup (module
`SimplyConnected.LeviCocenterKernelGenerationStatement`) implies the published
`RankOneLeviCocenterGenerationStatement` (module `SimplyConnected.RankOneLeviFactors`). It uses
only the standard axioms. It does not prove `LeviCocenterKernelGenerationStatement`.

## Implemented proof

Take the data of `RankOneLeviCocenterGenerationStatement`: `G`, `i`, `ν`, `j : M ⟶ G`, rank-one
Levi factors `a α : A α ⟶ G`, `d : D ⟶ M`, the cocenter `q : M ⟶ Q`, and for each simple
relative root `α` the derived subgroup `dα α`, the cocenter `qα α` of `M ∩ A α`, and `φ α`
with `subgroupIntersectionFst j (a α) ≫ q = qα α ≫ φ α`.

1. **Setup.** `j` is a closed subgroup, since it is isomorphic over `G` to the affine centralizer
   representative. `M` is connected reductive (`dynamicCentralizerReductive`), hence affine.
   `D` is semisimple (`derivedSubgroupSemisimple`), hence perfect (`semisimplePerfect`). The
   quotient `q` is flat and surjective, and it is quasi-compact because `M` is affine and `Q`
   is separated (`fieldSeparated`: every group scheme over a field is separated).
2. **Standard Levi subgroups.** For each `α`, `rankOneLeviFactor_derivedRetraction` (module
   `SimplyConnected.RankOneLeviCocenterStructure`) gives `ζ α`, `l α : L α ⟶ G`, `jL α`,
   `e α : E α ⟶ L α`, `aE α`, `pA α` and `δ α`. `cocenterQuotientExistence` gives an fppf
   quotient `r α : L α ⟶ R α` by the derived subgroup. The published
   `range_kernelι_le_comap_of_derived` and `SubgroupFunctor.quotientSubgroupHom` give
   `π α : Q ⟶ R α` with `q ≫ π α = jL α ≫ r α`.
3. **Kernel generation.** `hker`, applied to these data, gives
   `(rationalPoints.map q).range ≤ closure (⋃ α, ker (rationalPoints.map (π α)))`. So it
   suffices to show that the kernel of `π α` on rational points lies in the range of
   `rationalPoints.map (φ α)`; `Subgroup.closure_mono` and `Set.iUnion_mono` conclude.
4. **Kernels lie in the images.** Fix `α`.
   - `a α` is a closed subgroup, so the projection `M ∩ A α ⟶ M` is a closed immersion
     (`isClosedSubgroup_subgroupIntersectionFst`). Hence `M ∩ A α` is affine, and `qα α` is
     quasi-compact (`fieldSeparated` again).
   - `mono_of_cocenter_square` (module `SimplyConnected.RankOneLeviCocenterKernel`) shows that
     `φ α` is a monomorphism.
   - `mem_range_of_comp_eq_one`, applied on the test scheme `Spec k`, shows that a rational point
     `x` of `Q` with `x ≫ π α = 1` is `y ≫ φ α` for a rational point `y` of `Qα α`.

## Relation to the literature

The target statement adapts the computation `M/[M,M] ≅ ∏ T_Θ` in the proof of Theorem A of
Prasad–Raghunathan, *On the Kneser–Tits problem* (1985), printed p.110 (registered as
`prasad-raghunathan-1985-kneser-tits`). This module separates that computation into two parts:
- the absolute part, isolated as `LeviCocenterKernelGenerationStatement`, which rests on
  Borel–Tits, *Groupes réductifs* (1965), Proposition 6.8;
- the relative part proved here. It identifies the kernel of the map to the cocenter of the
  Levi subgroup of `α` with the image of the cocenter of `M ∩ A α`.
