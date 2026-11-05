# Proof: kernels of torus maps through which every root factors are central

Authors: Worker 1428 (Lean proof and first Markdown draft) and Worker 1398
(recheck against the published statement and submission).

`Langlands.GroupScheme.splitTorusKernelCentrality` proves the proposition
`Langlands.GroupScheme.SplitTorusKernelCentralityStatement.{u}` (module
`Rational/SplitTorusKernelCentralityStatement`). Let `G` be a smooth affine
group scheme over a field `k` with connected underlying space, `i : T ⟶ G` a
homomorphism from a split torus, and `t : T ⟶ T'` a homomorphism to any
commutative group scheme. If every root of `i` is `t ≫ α'` for a character
`α'` of `T'`, then the actual scheme kernel of `t`, mapped into `G` by `i`, is
central on every test scheme. The module proves three further results.

## Helper results

- `characterValue_comapHom_kernel`: for a homomorphism `f : S ⟶ Q` of
  commutative group schemes and a character `ψ` of `Q`, the pulled-back
  character `f ≫ ψ` (`characterLattice.comapHom`, `Torus/HomKernelDiagonalizable`)
  takes the value `1` at every point of the actual kernel of `f`.
- `actionWeightSpace_comapHom_le_kernel_lieInvariants`: for an action `b` of
  `S` on `G`, the weight space of a pulled-back character `f ≫ ψ` consists of
  Lie vectors fixed by the restricted action of the kernel of `f`. This is
  the argument of the published
  `AutomorphicAction.integralActionWeightSpan_le_kernel_lieInvariants`
  (`Rational/ActionLieRigidity`), with the previous helper in place of
  `characterValue_zsmul_kernel`.
- `isCentral_kernelι_comp_of_roots_comapHom`: the statement in the case of a
  homomorphism `f : S ⟶ Q` between split tori (as group schemes) such that
  every root of `i` is a pullback `f ≫ ψ`. Let `b` be the conjugation action
  of `S` on `G` through `i`, restricted to the kernel of `f`.
  1. Its Lie invariants are everything. The weight spaces of the conjugation
     action span `Lie(G)` (`iSup_actionWeightSpace_eq_top`, split `S`). They
     are the adjoint weight spaces (`actionWeightSpace_conjugation`). A
     nonzero weight space has weight `0` or a root, and both are pullbacks
     along `f`, so the second helper applies.
  2. The kernel of `f` is diagonalizable: the published
     `Diagonalizable.homKernelDiagonalizableIso` identifies it with
     `D(coker f*)`, whose character group is finitely generated
     (`Diagonalizable.homKernelLattice_fg`). Its structure map is affine:
     it is the kernel inclusion followed by the affine structure map of `S`,
     and the kernel inclusion is a closed immersion because `Q` is affine,
     hence separated.
  3. The published
     `AutomorphicAction.fixedSubgroup_eq_top_of_diagonalizable_lieInvariants_eq_top`
     (smooth connected `G`; it uses the representability of fixed points,
     their smoothness for diagonalizable groups, and `lieSubgroupEquality`)
     shows that the fixed subgroup of `b` is all of `G` on every test scheme.
  4. So every point of `G` is fixed by conjugation by every point of the
     kernel, after any change of test scheme. This is the centrality of
     `kernelι f ≫ i` (`mul_inv_eq_iff_eq_mul`).

## Main proof

The set of roots of `i` is finite (`IsSplitTorus.finite_relativeRoots`,
`Rational/RootSupportFiniteness`, with `relativeRoots_eq_roots`). Let `J` be
the index type of the roots and `Q` the split torus `𝔾_m^J`. The published
`IsSplitTorus.homOfCharacterMap` (`Torus/CharacterMapHom`) gives
`ρ : T ⟶ Q` whose character pullback sends the `j`-th coordinate character
to the root `j`, and an integral vector `m` to `∑ m_j • j`.

1. Every root is a pullback along `ρ`, so the previous theorem shows that
   the kernel of `ρ` maps centrally into `G`.
2. The kernel inclusion of `t` composed with `ρ` is zero. Characters
   separate homomorphisms into the split torus `Q`
   (`IsSplitTorus.hom_ext_of_characters`). For a character `χ` of `Q`, the
   pullback of `χ` along the composite is a sum of integer multiples of the
   roots restricted to the kernel of `t`. Each root is `t ≫ α'`, which
   vanishes on that kernel (`CommGroupScheme.kernelι_comp`).
3. So the kernel inclusion of `t` factors through the kernel of `ρ`
   (`CommGroupScheme.kernelLift`, `Torus/KernelCocharacters`), and centrality
   passes to it (`IsCentral.comp`).

`T'` is not assumed to be a torus. The proof uses `t` only through the
vanishing of the roots on its kernel.

## Provenance

The statement and its source argument are in the statement's Markdown (Milne,
*Algebraic Groups*, 2017, source `milne-2017-algebraic-groups`: Propositions
21.7 and 21.8, printed p.427; Theorem 12.9, printed p.233; Theorem 13.1,
printed p.254; Proposition 10.34, printed p.197). The Lean route follows the
argument given there: the intersection of the root kernels is diagonalizable,
acts trivially on the Lie algebra, and its smooth fixed subgroup is all of
`G`. Each geometric input is a published Library theorem.

Checked with `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
over Library commit `ee0c0dd6da0a631f199c2bc0aa6040eece98f41d` (diagnostic
`5038e889-eb01-4348-bd81-4a1a7599bcf1`, Lake build): 0 errors, 0 warnings;
the theorem's type is exactly `SplitTorusKernelCentralityStatement.{u}`;
axioms `propext`, `Classical.choice`, `Quot.sound`. Worker 1428's earlier
check on the previous base was diagnostic
`867aa636-871f-4e59-8502-a92f9b74c3cf`.
