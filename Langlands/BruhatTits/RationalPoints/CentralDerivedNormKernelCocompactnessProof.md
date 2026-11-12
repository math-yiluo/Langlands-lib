# Proof: central and derived points are cocompact in the rational norm kernel

Author: Worker 4312.

`Langlands.BruhatTits.RationalPoints.centralDerivedNormKernelCocompactness`
proves exactly the published proposition
`Langlands.BruhatTits.RationalPoints.CentralDerivedNormKernelCocompactnessStatement.{u}`
of [SmoothRealStructureStatement](SmoothRealStructureStatement.md), at every
universe `u`. The statement and its hypotheses are unchanged.

For every nonarchimedean local field `F`, of either characteristic, and every
actual group scheme `M` over `Spec F` with `hM : IsConnectedReductive M`, write
`K = Plancherel.rationalCommonNormKernel M`, `Z = schemeCenterPoints M` and
`D = (derivedSubgroup M).carrier (Over.mk (𝟙 _))`. These are subgroups of the
same actual point group `rationalPoints M`, which carries the canonical
`rationalPointTopology F M.X`. The theorem gives
`CompactSpace (K ⧸ (((Z ⊓ K) ⊔ D).subgroupOf K))`. Here `K` has the subspace
topology and the quotient has the quotient topology.

## Implemented proof

The Lean proof is one application of the published reduction
`centralDerivedNormKernelCocompactness_of_premises` (Worker 723), from
[CentralDerivedNormKernelCocompactnessReduction](CentralDerivedNormKernelCocompactnessReduction.md).
Its type is

```text
ReductiveCentralTorusSurjectivityStatement.{u} →
  Plancherel.TorusNormKernelCompactnessStatement.{u} →
    SmoothRationalPointOpenMapStatement.{u} →
      CentralDerivedNormKernelCocompactnessStatement.{u}
```

The proof supplies its three premises with these published, unconditional
proofs:

1. `Langlands.GroupScheme.reductiveCentralTorusSurjectivity`
   ([CentralTorusSurjectivityProof](../../GroupScheme/Reductive/CentralTorusSurjectivityProof.md),
   Workers 1383 and 1408). Over every field, a connected reductive group has
   a closed central torus `i : Z₀ ⟶ M`. For every actual derived-subgroup
   inclusion `d`, the multiplication map `subgroupProductMap i d` is
   surjective on underlying schemes.
2. `Langlands.Plancherel.torusNormKernelCompactness`
   ([TorusNormKernelCompactnessProof](../../Representation/Plancherel/TorusNormKernelCompactnessProof.md),
   Worker 1505). For every affine, locally finite type torus `T` over a
   nonarchimedean local field, `rationalCommonNormKernel T` is compact in
   `rationalPointTopology`.
3. `Langlands.AlgebraicGeometry.PointTopology.smoothRationalPointOpenMap`
   ([SmoothOpenMapProof](../../AlgebraicGeometry/PointTopology/SmoothOpenMapProof.md),
   Worker 1505). A smooth morphism of affine schemes over a nonarchimedean
   local field induces an open map on rational points, for
   `rationalPointTopology`.

The module adds no other mathematics. The final theorem uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Actual-point comparisons used

The reduction proves all group and topology comparisons; none is assumed.
For a fixed `F` and `M`, it runs as follows.

- **Derived subgroup and quotient.** The published
  `derivedSubgroupRepresentability` gives an actual closed inclusion
  `d : D' ⟶ M` with `IsDerivedSubgroup d`. In particular,
  `SubgroupFunctor.range d = derivedSubgroup M` on every test. By
  `derivedSubgroupSmoothness`, `D'` is smooth. `normalSubgroupQuotient` gives
  a smooth affine `Q` and a homomorphism `q : M ⟶ Q`. This `q` is a
  represented fppf quotient whose actual scheme kernel has range
  `derivedSubgroup M`.
- **The quotient is a torus.** Premise 1 and the Library theorem
  `torusImageClosedTorusStatement` show that `Q` is a torus
  (`isTorus_of_isFppfQuotient_derivedSubgroup`).
- **Openness on points.** `q` is smooth by
  `IsFppfQuotient.smooth_of_smooth_kernel`, because `D'` is smooth and `q` is
  quasi-compact. Premise 3 then makes `rationalPoints.map q : M(F) → Q(F)` an
  open map for the two canonical point topologies.
- **Kernel on rational points.** The fppf kernel condition gives this
  directly. If `q(x) = 1` for `x ∈ M(F)`, then `x` lies in `D`, the derived
  subgroup functor evaluated at `Over.mk (𝟙 _)`. No surjectivity of
  `rationalPoints.map q`, finite index or isogeny image on rational points is
  used.
- **Derived points lie in the norm kernel.** The statement does not assume
  `D ≤ K`. The reduction proves it
  (`derivedPoints_le_rationalCommonNormKernel`): every rational character
  restricts to zero along an actual derived inclusion.
- **Norm kernels.** `q` maps `K` into `rationalCommonNormKernel Q`. For each
  rational character `χ` of `Q`, the restriction `χ ∘ q` is a rational
  character of `M`. Premise 2 makes `rationalCommonNormKernel Q` compact.
- **Topological core.** `compactSpace_quotient_subgroupOf_of_isOpenMap`, from
  [OpenHomCocompactness](OpenHomCocompactness.md), applies with
  `G = M(F)`, which is a locally compact topological group, and the closed
  subgroup `K`. The subgroup is `H = (Z ⊓ K) ⊔ D`, which contains the kernel
  of `rationalPoints.map q` by `le_sup_right`. The lemma finds a compact
  `C ⊆ K` that meets every coset of the kernel inside `K`. The image of `C` in
  `K ⧸ H.subgroupOf K` is then everything, so the quotient is compact.

The central factor `Z ⊓ K` plays no further role. The core lemma only uses
that `H` contains the kernel of the point map, and that kernel already lies in
`D`. The `subgroupOf K` intersection is formed exactly as in the statement.

## Scope

The theorem covers both mixed and equal characteristic. Openness of the
point map is the only analytic input. This matters in positive characteristic,
where an inseparable isogeny can have infinite-index image on rational points,
as the statement Markdown records from Renard's 2010 errata.
The literature correspondence for the target is recorded in the statement
Markdown (Renard 2026, V.2.1–V.2.6 and V.3.19). The reduction Markdown records
the sources for its own route.
