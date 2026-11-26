# Depth-zero reduction and compact induction on KP building data

`Langlands.Geometry.Building.depthZeroConsumer` proves
`DepthZeroConsumerStatement` in an arbitrary universe.
Fix a facet \(x\) of a datum satisfying `KPBuildingDatum.SatisfiesGroupAxioms`.
The proof uses the neutral facet model and its specified special-fibre
quotient, with the canonical topology on \(G(F)\).

1. `ModelAxiomClauses.neutral_points` identifies the parahoric \(P_x\) with
   the zero-fixer at the facet index. Its compactness follows from
   `IntegralModel.isCompact_integralPoints_localField`. The open subgroup
   `KPBuildingDatum.parahoricOpenSubgroup` uses
   `IntegralModel.isOpen_integralPoints_localField`.
2. `FacetAxiomClauses.reductive_quotients` supplies the unipotent radical,
   its represented fppf quotient, and connected reductivity. The Library's
   `positivePoints_subgroupOf_normal`, `localField_isCompact_positivePoints`
   and `localField_isOpen_positivePoints` give normality inside \(P_x\) and
   compactness and openness of the radical preimage in \(G(F)\). Inside
   \(P_x\), the radical preimage is the inverse image under the subtype
   inclusion. This inclusion induces the subspace topology and its range
   contains the ambient radical preimage, so compactness pulls back by
   `Topology.IsInducing.isCompact_preimage'` and openness by continuity.
   For reduction, `henselianLocalRing_integer` supplies the Henselian
   instance, and the finite residue field is perfect. The proof applies
   `parahoricReduction_surjective`, `ker_parahoricReduction` and
   `finite_quotientPoints_of_isConnectedReductive`. It composes
   `QuotientGroup.quotientMulEquivOfEq` for the kernel equality with
   `depthZeroQuotientEquiv`. On the class of \(p\) this evaluates to the
   reduction of \(p\).
3. Inflation is composition with reduction by definition.
   `inflation_ker_apply` proves that each element of the radical preimage
   acts as the identity. `depthZeroInduction` is bundled in `SmoothRep`,
   which gives the smoothness of the compact induction.
4. At \(g\in G(F)\), the kernel map composes `Induction.unitMap`, the
   underlying linear map of the morphism, and `Induction.evalLinearMap`
   at \(g\). The unit map uses `isSmooth_inflation` and
   `localField_isOpen_congruenceSubgroup`. The operations on morphisms
   and evaluation make this construction linear. The formula
   `depthZeroInductionKernelEquiv_apply` identifies it with the underlying
   function of `depthZeroInductionKernelEquiv`. Injectivity follows from
   that equivalence, whose inverse realizes every intertwining kernel.
   `inflation_asModule_finite` gives finite generation over the group
   algebra, so `Induction.compactInductionFiniteTypeKernel` expresses
   membership in the range as two-sided equivariance and finite
   double-coset support.

The statement gives the source locators for these specializations of
Kaletha–Prasad and Vignéras. [DepthZeroConsumerStatement](Statement.md)
