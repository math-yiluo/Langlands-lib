# Smooth character-kernel centralizers and their integral Lie image

`Langlands.GroupScheme.RelativeRoot.kernelCentralizerStructure` proves the exact
published proposition `KernelCentralizerStructureStatement.{u}` for every
universe `u`. For a smooth affine group scheme `G` over any field, a split torus
`S`, a homomorphism `i : S ⟶ G`, and a nonzero character `a`, it constructs a
smooth closed representative of the actual centralizer of `ker(a)`. Its Lie
image is exactly `integralWeightSpan i a`, the sum of the weight spaces indexed by all integer
multiples of `a`, including weight zero.

The kernel is the existing scheme-theoretic character kernel. Its centralizer
is the published subgroup functor defined on every test scheme with fixedness
on every refinement. The conclusion uses the existing `HasLieImage` predicate
on actual dual-number identity-kernel points. No smoothness or reducedness of
the kernel, primitivity of the character, characteristic restriction, or
connectedness of the representative is assumed or concluded beyond the exact
target. The proof retains the target's nonzero-character premise, although
the imported arguments also apply to the zero character.

The implemented proof is a composition of published constructions and lemmas.
It first installs the given affine and smooth structures on `G`, affineness of
the split torus, and finite generation of the full quotient character group
`characterLattice S / ℤ a`. The quotient is not saturated; its torsion remains
present, including torsion divisible by the field characteristic.

The two inclusions
`kernelLieInvariants_le_integralWeightSpan` and
`integralWeightSpan_le_kernelLieInvariants` give equality of these submodules.
The reverse inclusion uses the split-torus weight decomposition; smoothness of
`G` supplies its local finite type hypothesis. The forward inclusion
specializes the weight equation to points of the actual kernel.

The published `fieldFixedSubgroupRepresentability` theorem, applied through
`kernelCentralizer_isClosedRepresentable_of_fieldFixed`, supplies a group
scheme `C`, an inclusion `j : C ⟶ G` representing that entire centralizer
functor, and a closed-immersion proof. Thus representability is obtained in the
conclusion rather than retained as a premise.

`Diagonalizable.kernelDiagonalizableIso` identifies the actual kernel with
the diagonalizable group of the full quotient lattice.
`kernelCentralizer_smooth_of_diagonalizableIso` transports the restricted
conjugation action across this isomorphism and applies the published theorem
`Diagonalizable.FixedSmooth.fixedSubgroupSmooth` to the supplied representative.
Transport preserves the all-test, all-refinement fixed subgroup functor. It
therefore proves smoothness of this same `C`, including when the kernel itself
is nonsmooth.

Finally, `kernelCentralizer_hasLieImage` identifies the centralizer's tangent
image with `kernelLieInvariants i a`. Rewriting by the established submodule
equality yields the exact integral-weight image required by the target.

This is an internal assembly by Worker 1279, with Worker 1299's contribution to
the quotient-kernel and reverse-weight argument imported from the published
support modules. The general representability and smoothness proofs are also
imported by their Lean names. There is no remaining general-theorem premise.
The literature context is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), Proposition A.8.10 and its use in Proposition 3.3.6
(printed pp.547–550 and pp.109–110), together with Kaletha–Prasad (2023),
Proposition 2.11.9 (printed pp.133–134). The registered corrections of
1 November 2024, PDF p.25, change notation without changing this conclusion.
