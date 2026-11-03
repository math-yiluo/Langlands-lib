# Intrinsic action eigenspaces and adjoint weight comparisons: proof

This file proves
`Langlands.GroupScheme.RelativeRoot.ActionWeightComparisonStatement` from
`Langlands.GroupScheme.Rational.WeightSemigroupStatement` at every universe
`u`, as the theorem
`Langlands.GroupScheme.RelativeRoot.actionWeightComparison`. The scope is the
statement's: any field `k`, any group scheme `G` over `Spec k` whose
structure morphism is affine, any commutative group scheme `S` over `Spec k`,
and any actual automorphic action of `S` on `G` (respectively any
homomorphism `S → G`). No torus, splitness, smoothness or connectedness
hypothesis is used, and both conjuncts keep every coefficient algebra `A/k`
and the actual dual-number identity-kernel points.

The comparison is internal infrastructure for the CGP and KP sources cited in
`WeightSemigroup.md` (CGP §3.3; KP §2.11). It is the routine fact that the
weight vectors for a linear action form a subspace; the proof below is
derived from the Library constructions rather than transcribed from either
source.

## Naturality lemmas

`act_affineMap` shows that an automorphic action commutes with every change
of test algebra `f : A → B`: both sides are precompositions with the spectrum
map of `f`, so this is the published `AutomorphicAction.naturality`.
`affineMap_epsilonScaleAlg_constant` shows that epsilon scaling `ε ↦ cε`
fixes every constant dual-number point, because the scaling algebra map
restricts to the identity on `A`. Together they give
`act_constant_lieKernelScale`: the action of a constant point commutes with
epsilon scaling on the identity kernel.

## Eigenvectors form a subspace

The set `actionEigenvectors b χ` contains zero, since coefficient change,
the action of a point and epsilon scaling all fix the identity
(`zero_mem_actionEigenvectors`). It is closed under addition, which is the
kernel group law, because all three operations are group homomorphisms
(`add_mem_actionEigenvectors`, using `AutomorphicAction.act_mul_right`). For
closure under scalars `c ∈ k` (`smul_mem_actionEigenvectors`), coefficient
change turns epsilon scaling by `c` into epsilon scaling by its image in
`A` (`lieKernelMap_scale`). The action then commutes with this scaling by
`act_constant_lieKernelScale`. The eigenvector equation gives scaling by
`χ(s)`, and the two scalings commute because `lieKernelScale_mul` turns their
composite into scaling by a product in the commutative ring `A`.

`coe_actionWeightSpace` follows by span induction: the span is contained in
the eigenvector set, and the reverse inclusion is `Submodule.subset_span`.
This is the first conjunct. `mem_actionWeightSpace_iff` restates it for
membership.

## Conjugation and the adjoint weight spaces

`actionWeightSpace_conjugation` proves the second conjunct by submodule
extensionality. By `mem_actionWeightSpace_iff` and `mem_weightSpace`, both
memberships quantify over the same algebras `A` and points `t ∈ S(A)`. For
conjugation, `AutomorphicAction.conjugation_act` gives the action of the
constant point of `t` as conjugation by the composite of that constant point
with `i`. This composite is the constant point of `i(t)`, by associativity of
precomposition. The adjoint action `adjoint G A (i(t))` is the same
conjugation by `adjoint_val`, and the module scalar `χ(t) •` is
`lieKernelScale` by definition. The two conditions therefore express the
same equality of underlying points, read through `Additive` and the kernel
subtype.

The final theorem applies these two lemmas, passing the affine-structure
hypothesis `hAff` of the statement as the instance argument.
