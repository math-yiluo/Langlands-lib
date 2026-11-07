# Hermitian approximation on `L²([G])` and its cuspidal subspace: proof

Authors: Worker 112 and Worker 1841.

The theorem
`Langlands.Global.RestrictionSplitCentre.quotientFullAEL2HermitianApproximation`
has type exactly the published
`QuotientFullAEL2HermitianApproximationStatement`. It is the `[G]`
counterpart of the published positive-torus proof in
`GroupSchemeFullAEL2HermitianApproximationProof`. The only difference is that
it gets the ambient approximation directly from the published generic theorem
`Langlands.Analysis.rightHaarHermitianApproximation`, not from a separate
`[G]` proof module.

## Proof

After introducing the data and hypotheses of the statement, write
`μG = Measure.haar` on the adelic points `AdelicGroupPoints F G`, `Sq` for the
published closed almost-everywhere cuspidal submodule
`quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT` of `L²([G])`, and
`π = rationalQuotientL2BoundedRightAction F G (quotientHaarMeasure F G S j) hInv'`
for the published bounded right action on `L²([G])`.

1. Every operator `π a` preserves inner products. This follows from the
   published norm preservation `norm_rationalQuotientL2BoundedRightAction` by
   Mathlib's polarization equivalence `LinearMap.norm_map_iff_inner_map_map`.
2. Every orbit `a ↦ π a x` is continuous. This is the published continuous
   orbit map `rationalQuotientL2OrbitMap F G hInv' h hi hc hT x`, which uses
   the hypotheses `h`, `hi`, `hc`, `hT` and the norm-one right invariance
   instance.
3. `rightHaarHermitianApproximation μG π` applies to these two facts: the
   adelic points already carry the locally compact, Hausdorff, second
   countable Borel topological group structure it needs, and `L²([G])` is
   complete. It returns the weights `f n`, their `μG.inv`-integrability,
   continuity, compact support, nonnegativity, unit integral, modular symmetry
   and shrinking supports. It also says that the generic integrated operators
   `integratedIsometricAction μG.inv π …` are symmetric contractions converging
   strongly to the identity. By definition these generic operators are the
   published `rationalQuotientL2IntegratedAction` operators `A n` of the
   target, so the two operator facts are stated for `A n` by definitional
   unfolding. The generic conclusion about invariant closed subspaces is
   discarded. This gives the first four conjuncts of the target.
4. Let `B n` be the published integrated action
   `quotientFullAEL2CuspidalIntegratedAction` on `Sq` for the same weights. The
   published `quotientFullAEL2CuspidalIntegratedAction_val` says that
   `(B n ψ).val = A n ψ.val`. This is the value-identity conjunct.
5. `B n` is symmetric. The inner product on `Sq` is that of `L²([G])`, so
   symmetry carries over from `A n` through the value identity.
6. `‖B n‖ ≤ 1` follows from `ContinuousLinearMap.opNorm_le_bound`, because
   `‖B n ψ‖ = ‖A n ψ.val‖ ≤ ‖A n‖ ‖ψ.val‖ ≤ ‖ψ‖`.
7. `B n ψ → ψ` in `Sq`. Convergence in a subtype is convergence of the values
   (`tendsto_subtype_rng`), and the values are `A n ψ.val → ψ.val`.
8. The two projection identities are the published
   `quotientFullAEL2CuspidalOrthogonalProjection_integratedAction` and
   `quotientFullAEL2CuspidalAmbientProjection_integratedAction`, applied to the
   same weights.

## Scope

The same weight sequence serves both the ambient space and the cuspidal
subspace. As in the target, the weights are continuous functions on the full
group `G(A_F)`, not smooth functions on `A_G \ G(A_F)`. The group integration
measure is the inverse `μG.inv` of Mathlib's left Haar measure, and the
quotient measure `quotientHaarMeasure F G S j` is unchanged. The proof does
not identify left and right Haar measures. It asserts nothing about smooth
vectors, compactness, trace class, spectral decomposition, finite volume or
reduction theory.

## Provenance

This is an internal adapter proof. It imports two published modules by their
Lean module names: the target
`Langlands.Automorphic.GroupSchemeRestrictionFullAEL2HermitianApproximationStatement`
and `Langlands.Representation.Unitary.RightHaarHermitianApproximationProof`.
It combines two unreviewed drafts by Worker 112 from revision 4 of the
parent's shared draft: the full-a.e. cuspidal adapter and the `[G]`
specialization of `rightHaarHermitianApproximation`. The second is the draft
of the separate proof of `QuotientL2HermitianApproximationStatement`. Worker
1841 inlined that specialization here so the proof does not depend on that
unpublished module. The submitted contribution contains only this proof's
Lean/Markdown pair.
