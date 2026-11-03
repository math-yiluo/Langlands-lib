# Positive-multiple inclusion for intrinsic root subgroup functors

This internal result proves inclusion for the published, actual
`RelativeRoot.subgroup` construction over every base scheme in universe `u`.
For any commutative acting group scheme, ambient group scheme, homomorphism
`i`, character `a`, and positive natural number `n`, it proves
`subgroup i (n • a) ≤ subgroup i a`. The inequality is inclusion on every test
scheme. The named Prop-valued statement
`RootSubgroupMultipleInclusionStatement` records this full scope, and
`rootSubgroupMultipleInclusion` proves it.

The proof uses the intrinsic orbit-extension definition from `RootSubgroup`.
If a point has an extension `e` through the character `n • a`, then
`e(t^n)` is an extension through `a`. The lemma
`character_comp_powerHom` identifies the composite of `a` with the power
homomorphism of the multiplicative group with its additive multiple.
`IsOrbitExtension.of_nsmul` uses the published
`AffineLine.unitInclusion_comp_powerMap` to verify the orbit identity.
That identity holds for every natural `n`; positivity is used separately
when verifying the value at zero.

For `n > 0`, the published
`AffineLine.evalZero_whiskerLeft_powerMap` identifies the value of `e(t^n)`
at zero with that of `e`. This proves `subgroup_nsmul_le`.
Its specialization `double_subgroup_le` gives the doubled-character inclusion
over the same arbitrary base, independently of smoothness, reductivity,
splitness, actual root membership, or any structural source proposition.

The provenance is a direct derivation from the existing orbit construction,
the existing affine-line monomial maps in `RootSubgroupPositive`, and the
existing pointwise character-lattice operations in `Torus.Lattice`.
It does not use a new literature premise. This strengthens the inclusion part
of `RootSubgroupCentrality.double_subgroup_le_of_cyclicComparison` by removing
all its structural hypotheses. Centrality, vector structures and represented
fppf quotients remain separate proof obligations; this result does not prove
the full `RootSubgroupVectorStatement`.
