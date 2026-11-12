# Proof of `Langlands.GroupScheme.NormalSubgroupAffineKernelStatement`

This module proves the published proposition `Langlands.GroupScheme.NormalSubgroupAffineKernelStatement` (module `Langlands.GroupScheme.AffineKernelQuotient`) at every universe `u`. The statement says that every closed normal subgroup `i : N ⟶ G` of a smooth affine group scheme `G` over a field is the kernel of a homomorphism `f : G ⟶ H` with `H` affine and locally of finite type, in the sense `range (kernelι f) = range i`.

The theorem is `Langlands.GroupScheme.normalSubgroupAffineKernel : NormalSubgroupAffineKernelStatement.{u}`, with no hypotheses.

## Proof

A short tactic proof: the published `normalSubgroupQuotient` gives a smooth affine `Q` and an fppf quotient `q : G ⟶ Q` by `range i`. Take `H = Q` and `f = q`: the affine structure map is given, local finite type follows from smoothness by instance search, and the last component of `RelativeRoot.IsFppfQuotient` is the kernel equation `range (kernelι q) = range i`.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.normalSubgroupQuotient` (module `Langlands.GroupScheme.NormalSubgroupQuotientProof`)
