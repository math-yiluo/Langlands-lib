# Smooth moduli of actual closed torus subgroups

Author: Worker 1421.

This module proves the target of task `45ac6e52-a4d8-4414-91f1-03c3be35223e`,
the Library statement
`Langlands.GroupScheme.TorusSubgroupModuli.SmoothTorusSubgroupRepresentabilityStatement.{u}`.
A smooth affine group scheme `G` over any base scheme `S` has a smooth
parameter scheme `M → S` carrying a universal family `j` of closed
relative-torus subgroups of `G`.

## Proof

The proof composes three implications from the Library
(`TorusSubgroupChartStatements`):

- `finiteTypeChartCover : FiniteTypeChartCoverStatement.{u}` (this module): over
  every affine base `Spec R` of finite type over `ℤ`, every smooth affine group
  has a family of open charts covering the closed tori over field points. It
  is `TorusChart.finiteTypeChartCover_of` (module `TorusChartCover`), with its
  three hypotheses discharged by Worker 950's published results:
  - the étale splitting statement `TorusChart.EtaleSplitStatement` is
    `HomScheme.exists_etale_splitPoints` (module `TorusSubgroupSplitting`),
    whose statement is the same;
  - smoothness of the coordinate Hopf algebra of a smooth affine group is
    `HomScheme.FiniteDiagonalizable.smooth_hopfAlgebra` (module
    `FiniteDiagonalizableSmooth`);
  - smoothness of the representing algebra `W R A r m`, which is
    `FiniteBialgebraHom.HomAlgebra R A R[(ℤ/m)^r]`, is the instance
    `FiniteBialgebraHom.smooth_homAlgebra` (module
    `Langlands.Algebra.DiagonalizableHomSmooth`). It applies because a smooth
    algebra is formally smooth and finitely presented, and `(ℤ/m)^r` is
    finite.
- `chartCoverReduction : ChartCoverReductionStatement.{u}` (published, module
  `TorusSubgroupChartCoverReductionProof`) turns this into chart covers over
  every base scheme.
- `chartGluing : ChartGluingStatement.{u}` (published, module
  `TorusSubgroupChartGluingProof`) glues a chart cover into the smooth moduli
  scheme.

`smoothTorusSubgroupRepresentability` is
`chartGluing (chartCoverReduction finiteTypeChartCover)`.

## The chart construction

The modules written for this task, in dependency order, are:

- `Algebra/`: `FiniteSubcomodule`, `HopfPointExtension`,
  `LatticeConfigurationBound`, `HopfPointRigidity`, `HopfPointWeightWindow`,
  `HopfPointWindowExtension`, `HopfPointBridge`, `HopfPointTwist`,
  `HopfPointClosedLocus`, `HopfPointKernel`, `InvariantPrincipalOpen`,
  `TorusChartAlgebra`, `HopfPointConnected`, `TorusChartRing`,
  `HopfPointWeightLocus`, `TorusChartExistence`;
- `AlgebraicGeometry/SpecRingActionFree`;
- `GroupScheme/HomScheme/`: `SplitTorusRangeKernel`, `TorusChartDescent`,
  `TorusChartConstruction`, `TorusChartInjective`, `TorusChartOpen`,
  `TorusChartCover`.

Each module has its own Markdown description. The construction runs as
follows:

1. The ambient Hopf algebra `A` has a finite subcomodule `V` of generators with
   a bounded presentation.
2. For `m` large compared with a box of weights, a homomorphism
   `μ_m^r → Spec A` whose weights on `V` lie in the box extends uniquely to a
   homomorphism of `G_m^r` (the extension lemma, `HopfPointExtension`). It
   does so over a principal open of the parameter algebra `W` of
   homomorphisms `μ_m^r → Spec A`.
3. The closed-immersion and weight-window conditions are open
   (`HopfPointClosedLocus`, `HopfPointWeightLocus`).
4. The chart is the quotient of an invariant principal open of `Spec W` by the
   free action of `Aut((ℤ/m)^r)` (`TorusChartConstruction`), with the torus
   descended from the extension.
5. Injectivity of the chart comes from rigidity of tori with the same image
   (`HopfPointKernel`, `HopfPointConnected`). Openness comes from the étale
   splitting of closed tori and the uniqueness of extensions
   (`TorusChartOpen`).
6. Every closed torus over a field lies on some chart (`TorusChartExistence`,
   `TorusChartCover`).
