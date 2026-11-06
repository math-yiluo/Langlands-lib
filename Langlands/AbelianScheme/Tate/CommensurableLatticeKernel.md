# Kernel subgroup attached to a commensurable full Tate lattice

This is an internal construction from the actual full Tate module and its torsion-kernel comparison. It combines `CommensurableLatticeTorsion`, `CommensurableLatticeScaling`, and `TorsionSubgroupQuotient`; it asserts no additional theorem from external literature. The construction and proofs are uniform in the scheme universe.

## Actual kernel points and monodromy

For a commutative group object `G` over `S`, a test scheme `T`, a positive full index `n`, and an additive subgroup `L` of `RationalFull G T`, `normalizedKernelSubgroup` is an additive subgroup of the actual `T`-points of the kernel of multiplication by `n²`. It is the inverse image of `normalizedLevelSubgroup G T n L` under `kernelLevelEquiv`. That level subgroup is the evaluation image, at `n²`, of the integral families whose rationalizations belong to `nL`. The membership lemma is definitional.

For an abelian scheme `A` and a field-valued point `s`, `normalizedKernelSubgroup_monodromy` assumes finite geometric fibres `hs`, the torsion finite étale statement, invertibility on the base of every positive integer, and invariance of `L` under rational monodromy. After installing the actual multiplication kernel's finite and étale instances from those assumptions, it proves invariance of the kernel-point subgroup under `groupMonodromy`. The proof transports the action through `levelMonodromy_kernel` and applies the previously established invariance of the normalized level subgroup. Connectedness and algebraic closedness are not hypotheses of this conditional transport lemma.

## Conditional construction of the abelian scheme

`exists_realization_of_normalizedKernelSubgroup` assumes that `S` is locally noetherian and that every finite set of points of `A` lying in one fibre lies in an affine open of `A`. Fix a positive index `n` and an additive subgroup `L` of the actual rational full Tate module at `s`. The two bounds are:

- For each integral family `x`, `n · toRational(x)` belongs to `L`.
- For each `w ∈ L`, the element `n · w` is the rationalization of an integral family.

The remaining supplied data are an actual finite étale commutative group scheme `H` and an actual group homomorphism from `H` into the multiplication-by-`n²` kernel of `A`. Its underlying scheme map is a closed immersion. The hypothesis `hM` says exactly that its point image at `s` equals `normalizedKernelSubgroup`; it is not an assumed equality of full Tate images.

The conclusion constructs an actual abelian scheme `B`, an isomorphism `e : Rationalization.of B ≅ Rationalization.of A`, and, for every `w`, the equivalence between `w ∈ L` and the existence of a full integral family of `B` whose canonical rationalization maps to `w` under `rationalHomMap e.hom`. Thus the full index predicate is retained throughout.

The proof composes the supplied kernel inclusion into `A` using `ofTorsionSubgroup`, obtaining an actual finite étale subgroup `K` killed by `n²`. The published quotient-existence theorem, with precisely the affine-open fibre hypothesis above, supplies actual quotient data `D`. Its reverse map `r : D.B → A` has both composites with the quotient map equal to multiplication by `n²`.

For each integral family `x`, the exact reverse-map image criterion in `TorsionSubgroupQuotient` identifies membership in the image of `T(r)` with the inclusion-image condition at the `n²` coordinate. The kernel-level equivalence and the actual composite inclusion identify that condition with `hM`. Finally, `evaluation_mem_normalizedLevelSubgroup_iff`, using the lower bound, identifies it with membership in `normalizedIntegralSubgroup`. The rational isomorphism is then `squareReverseIso`, with forward map `r/n`; `squareReverseIso_image_iff`, using the upper bound and the established integral-image equality, gives the required rational image.

This module leaves the existence of `H` and its closed immersion with the exact finite point image as an explicit input to the conditional construction. Proving such a finite subgroup realization and applying it to the invariant subgroup above remain obligations of the full lattice-realization theorem. No rank, torsion-geometry, or finite-subgroup existence assertion is inferred here.
