# NYLL M004.007: the cyclic norm-kernel vanishing target

The paired Lean file gives the Prop-valued target
`Langlands.NYLL.CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZeroStatement`
for source theorem
`CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero`.
The source is Naganori Yamaguchi's ClassFieldTheory at
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, M004.007,
lines 121–146 (signature at 126–131), with section context at 26–32.
The file SHA-256 is
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The parameters are the source's implicit `G : Type`, `[Group G]`,
`[Fintype G]`, and explicit `A : Rep.{0} ℤ G`, `g : G`,
`hg : ∀ x, x ∈ Subgroup.zpowers g`, and
`hzero : CategoryTheory.Limits.IsZero (tateCohomology A (-1))`, in that
order. The group and representation carrier remain in universe zero.
The target says that for every `x : A.V` with `A.norm.hom x = 0`,
there is `y : A.V` satisfying `A.ρ g y - y = x`.
These are Mathlib's actual representation norm, action and Tate
cohomology object. No separate kernel-containment premise is assumed.

Worker 120 extracted the theorem signature, prefixed the namespace,
appended `Statement`, and made the conclusion the body of a `def`
returning `Prop`. The argument names `hg` and `hzero` gain leading
underscores because the definition's body does not refer to the proofs;
both parameters and their full types are retained. The source's unused
universe declaration and unrelated declarations are omitted, and
`CategoryTheory.Limits.IsZero` is qualified. The only required import is
`Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`.
A private complete-source theorem assignment checks the entire adapted
telescope and conclusion, and a direct proposition equality is proved
by `rfl`. Focused compilation and proposition inspection establish
that no earlier M004 or M003 construction is needed to state this target.

This unit states M004.007 without proving it. Its separate proof can use
the finite-cyclic comparison M004.006 after that construction is published.
The extension data and vanishing-condition predicate M004.002–005 remain
separate. No host reciprocity or cohomological theorem is asserted here.

The original copyright, Apache-2.0 release and author header are retained.
The retained files are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
