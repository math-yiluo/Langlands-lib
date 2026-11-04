# Smooth affine quotients by normal closed subgroups

Authors: Worker 1228 and Worker 1280. Worker 1228 supplied the character
cancellation and exact-kernel representation; Worker 1280 supplied the affine
image quotient, quotient comparison and effective descent reduction. Worker 1228
assembled these constructions into the exact target proof.

`Langlands.GroupScheme.normalSubgroupQuotient` proves the unchanged published
`Langlands.GroupScheme.NormalSubgroupQuotientStatement.{u}` for every universe
`u`. For a smooth affine group `G` over an arbitrary field `k : Type u`, every
closed normal subgroup `i : N ⟶ G` is the full represented kernel of a flat,
surjective, locally finitely presented homomorphism to a smooth affine group.
No smoothness condition on `N`, perfectness of `k`, characteristic restriction,
connectedness or splitness assumption is added.

The helper `algClosedNormalSubgroupAffineKernel` proves the construction input
of the existing algebraically closed reduction. Over an algebraically closed
field, smoothness makes the ambient scheme reduced and its structure map
locally of finite type. `normalKernelRepresentation` then constructs an actual
finite matrix representation with precisely `SubgroupFunctor.range i` as the
range of its scheme-theoretic kernel, on every scheme test. The target is the
existing general linear group scheme. Its published smoothness gives local
finite type, and its existing affine model gives affineness.

The imported reduction passes to `AlgebraicClosure k` in the same universe,
forms the actual affine schematic image of this representation, and obtains
its fppf image projection with the prescribed full kernel. Canonical comparisons
of quotients with the same kernel give its Cech descent datum. Effective affine
fpqc descent gives the group and quotient map over the original field and
reflects the full represented-kernel equality. Smoothness of the original
source makes the descended quotient target smooth. Applying that reduction to
the discharged algebraically closed-field input proves the exact published
target, including imperfect fields and nonsmooth normal subgroups.

This is an internal composition of the implemented representation, image and
affine descent constructions. The detailed character and fixed-tensor argument
is in `MatrixRepresentation/NormalKernel.md`; the quotient descent argument is
in `NormalSubgroupQuotientAlgClosedReduction.md` and its imported helper pairs.
The target's Lean/Markdown pair and all its imports are unchanged. This proof
uses the effective affine descent route documented in those helpers and does
not claim to reproduce the target source's proof line by line.
