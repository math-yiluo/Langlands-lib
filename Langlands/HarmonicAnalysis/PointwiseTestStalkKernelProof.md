# Original-module stalk kernel and vanishing-test generators

This module proves the published proposition
`Langlands.HarmonicAnalysis.PointwiseTestModule.NondegenerateStalkKernelStatement`
as `nondegenerateStalkKernel`, with independent universe parameters `uX` for
the space and `uM` for the original module. It retains every hypothesis of the
target: a locally profinite space and a nondegenerate nonunital action of its
pointwise test algebra on an additive commutative group.

## Implemented proof

The first equivalence reuses the published, independent-universe theorem
`ProjectorStalk.annihilatorDescription`. A compact basis open is a compact
clopen subset because the space is Hausdorff; conversely a compact clopen
subset defines a compact basis open. The associated characteristic test and
its original action are unchanged by this translation.

For the forward additive-closure inclusion, choose a neighborhood indicator
`a` annihilating the vector `m`, and use
`PointwiseTestModule.exists_characteristic_fixer` to obtain an indicator `e`
fixing `m`. The actual test `g = e - a * e` vanishes at the point and satisfies
`g • m = m`, so `m` itself is one of the generators. The proof uses the
endomorphism homomorphism of the supplied nonunital action to distribute
subtraction; no unit law on that action is assumed.

For the reverse inclusion, use the additive subgroup underlying the published
literal `ProjectorStalk.annihilatorSubmodule`. If a test `f` vanishes at the
point, its local constancy and the compact-open basis give a compact open
neighborhood on which it is zero. The neighborhood indicator is nonzero at
the point and annihilates `f • m'`, because its product with `f` is zero.
Thus every generator belongs to the literal annihilator subgroup. The
minimality of `AddSubgroup.closure` gives the required inclusion.

The proof installs the canonical complex module only to use the existing
annihilator submodule. It derives this module from nondegeneracy and retains
the original test action. It assumes no complex module on the input carrier
and imposes no relation between the two universe parameters.

## Source and derived scope

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 reread II.2.5, printed pp.40–42 / PDF pp.46–48, when preparing
this proof.

The first clause is the original-module stalk-kernel description on
printed pp.40–41. The second is the module-side formulation of the
vanishing-test span in the compact-section stalk Remark on printed p.42,
through the preceding equivalence between nondegenerate test modules and
sheaves. This derived provenance is part of the unchanged target's
explanation. The implemented subtraction argument is an alternate direct
module proof of the same generated-subgroup equality.

This focused result proves the exact two equivalences. The richer
projector-stalk colimit and quotient comparisons remain the separately
published results of `ProjectorStalkProof`.
