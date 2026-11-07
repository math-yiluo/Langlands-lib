# Realization of commensurable invariant full Tate lattices

Authors: Worker 1730 and Worker 1575.

The theorem
`Langlands.AbelianScheme.Tate.commensurableInvariantLatticeRealization`
proves exactly
`Langlands.AbelianScheme.Tate.CommensurableInvariantLatticeRealizationStatement.{u}`.
It constructs an actual abelian scheme B over the entire given base S and a
rational isomorphism from B to A whose full integral Tate image is precisely
the prescribed integral finite-adele submodule L. The theorem is uniform in
the universe u and has no additional premises.

## Implemented proof

Choose the positive integer n supplied by the two commensurability bounds:
`n im(TA) ⊆ L` and `n L ⊆ im(TA)`. The proof forms the actual commutative
group scheme G that is the kernel of multiplication by n² on A. The original
torsion-geometry hypothesis and invertibility of positive integers on S
supply the finite and étale instances for G.

The helper `normalizedKernelSubgroup_monodromy` proves monodromy invariance
of `normalizedKernelSubgroup` inside the actual geometric point group of G.
This subgroup is obtained from the n²-coordinate evaluation image of the
integral families whose rationalizations belong to n L, transported through
the actual kernel-point equivalence. The given rational monodromy invariance
of L supplies its invariance.

The published theorem
`Langlands.AlgebraicGeometry.FiniteEtale.invariantSubgroupRealization`
then constructs an actual finite étale commutative group scheme H and a
closed immersion into G whose geometric point image is exactly this subgroup.
Its hypotheses are provided by the original connected locally noetherian
base, algebraically closed geometric point, explicit finite geometric fibres,
and the finite étale structure of G. Thus no subgroup realization or
point-image comparison is added as an input.

With these objects and instances, the proof applies
`exists_realization_of_normalizedKernelSubgroup`. This published helper
composes the subgroup inclusion into A and applies
`FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre`
using the original finite-set fibre-affineness hypothesis. It obtains an
actual quotient abelian scheme B with quotient map q. The reverse-map
construction of Worker 1575 descends multiplication by n² to an actual map
r from B to A, with both composites with q equal to multiplication by n².
The rational isomorphism has forward map r/n and inverse q/n.

The same helper computes the full integral image of the reverse map using
`exists_map_inverseMultiple_iff_exists_inclusion`: an integral family lies in
that image exactly when its n²-coordinate belongs to the realized subgroup.
`evaluation_mem_normalizedLevelSubgroup_iff`, using the lower bound, identifies
this condition with membership in the integral preimage of n L. Finally,
`squareReverseIso_image_iff`, using the upper bound, proves that the image
under r/n is exactly L. The full index predicate is `fun _ => True` throughout.
The full-index evaluation and image calculations reuse the published
infrastructure rather than reprove evaluation surjectivity or integral-image
reflection.

## Provenance and scope

This is an internal derived proof of the published realization target. It
imports the target, `CommensurableLatticeKernel`, and the generic invariant
subgroup proof by Lean module name. The construction retains all original
hypotheses, including the torsion statement, coefficient comparison, integer
invertibility, geometric point, finite-fibre condition and source
fibre-affineness condition. L is passed to the helper as its additive
subgroup, preserving membership and both bounds. The finite étale subgroup,
quotient, realizing abelian scheme, rational isomorphism and both directions
of the exact full Tate-image comparison are derived conclusions.

No rank, polarization, determinant, moduli or representability assertion is
made. The Harris specialization and the existing infrastructure suspension
boundaries remain outside this theorem. No additional external literature
claim is asserted.
