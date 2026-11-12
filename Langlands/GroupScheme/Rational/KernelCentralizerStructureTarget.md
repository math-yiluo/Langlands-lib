# The kernel-centralizer structure target

`Langlands.GroupScheme.RelativeRoot.kernelCentralizerStructure`
proves the published proposition
`Langlands.GroupScheme.RelativeRoot.KernelCentralizerStructureStatement.{u}`
(module `Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`) for
every universe `u`. The theorem's type is exactly that proposition with its
complete hypothesis scope. For a smooth affine group scheme `G` over any field
`k`, a split torus `S`, a homomorphism `i : S ⟶ G` and a nonzero character `a`,
the statement asks for a smooth closed subgroup `j : C ⟶ G` that represents
the all-test centralizer functor `kernelCentralizer i a` of the scheme-theoretic
kernel of `a`. Its Lie image must be exactly `integralWeightSpan i a`, the sum
of the weight spaces indexed by all integer multiples of `a`, including weight
zero.

## Proof

The module re-exports the published Library theorem
`Langlands.GroupScheme.RelativeRoot.kernelCentralizerStructure`
(module `Langlands.GroupScheme.Rational.KernelCentralizerStructureProof`) at
the same universe `u`. The independently reviewed alias is consolidated into
that existing declaration. That theorem already has the type
`KernelCentralizerStructureStatement.{u}`. This module adds no hypotheses or
new constructions. It also does not change the statement or the modules it
imports.

The imported theorem's own Markdown explains its proof. In outline, the
proof proceeds as follows:

- Published field-fixed-subgroup representability gives a closed
  representative `C` of the centralizer functor.
- Smoothness of `C` comes from the published smoothness of fixed subgroups of
  diagonalizable actions. This uses the identification of the kernel with the
  diagonalizable group of the full quotient lattice `characterLattice S / ℤ a`.
- The Lie image is `kernelLieInvariants i a`. The two published inclusions
  between that submodule and `integralWeightSpan i a` show the two are equal.

The kernel may be nonsmooth. No primitivity of `a`, characteristic
restriction or connectedness is assumed.

## Credits and provenance

This module was written to close Task 3843 with an artifact reviewed in the
current instance. The mathematical work is in the imported Library theorem,
which was carried over from the previous instance. That theorem's Markdown
credits Worker 1279 with the internal assembly. It credits Worker 1299 with
the quotient-kernel and reverse-weight argument in the published support
modules. Those are previous-instance worker names. They are not identities in
this instance, so they appear here as credits only.

The literature context is the same as for the imported theorem:

- Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
  Proposition A.8.10 and its use in Proposition 3.3.6 (printed pp.547–550 and
  pp.109–110).
- Kaletha–Prasad (2023), Proposition 2.11.9 (printed pp.133–134).
