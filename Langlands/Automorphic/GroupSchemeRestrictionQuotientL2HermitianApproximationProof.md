# Hermitian approximation of the right action on `L²([G])`: proof

Author: Worker 112.

The theorem
`Langlands.Global.RestrictionSplitCentre.quotientL2HermitianApproximation`
has type exactly the published
`QuotientL2HermitianApproximationStatement`. It is the `[G]` counterpart of
the published positive-torus proof `groupSchemeQuotientL2HermitianApproximation`
and follows the same route.

## Proof

After introducing the data and hypotheses of the statement, the proof takes
`μG = Measure.haar` on the adelic points `AdelicGroupPoints F G` and the
published bounded right action
`π = rationalQuotientL2BoundedRightAction F G (quotientHaarMeasure F G S j) hInv'`
on `L²([G])`. It applies the published generic theorem
`Langlands.Analysis.rightHaarHermitianApproximation` to `μG` and `π`, which
needs two facts:

- every operator `π a` preserves inner products. This follows from the
  published norm preservation `norm_rationalQuotientL2BoundedRightAction` by
  Mathlib's polarization equivalence `LinearMap.norm_map_iff_inner_map_map`;
- every orbit `a ↦ π a x` is continuous. This is the published continuous
  orbit map `rationalQuotientL2OrbitMap F G hInv' h hi hc hT x`, which uses the
  hypotheses `h`, `hi`, `hc`, `hT` and the norm-one right invariance instance.

The adelic points already carry the locally compact, Hausdorff, second
countable Borel topological group structure that the generic theorem needs,
and `L²([G])` is complete.

The generic theorem returns the weights `f n`, their `μG.inv`-integrability,
continuity, compact support, nonnegativity, unit integral, modular symmetry,
shrinking supports, and symmetric contractions converging strongly to the
identity. The generic integrated operators are by definition the published
`rationalQuotientL2IntegratedAction` operators of the target. The generic
theorem also returns a statement about invariant closed subspaces, which this
target does not need; it is discarded.

## Scope

The group integration measure is the inverse `μG.inv` of Mathlib's left Haar
measure; the quotient measure `quotientHaarMeasure F G S j` is unchanged. The
proof does not identify left and right Haar measures. As in the target, the
weights are continuous functions on the full group `G(A_F)`, not smooth
functions on `A_G \ G(A_F)`.

## Provenance

This is an internal adapter proof. It imports the published target and the
published `Langlands.Representation.Unitary.RightHaarHermitianApproximationProof`
by their Lean module names. The submitted contribution contains only this
proof's Lean/Markdown pair.
