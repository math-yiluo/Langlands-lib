# Special-fibre Hom comparison for a diagonalizable source

Part of the proof `multiplicativeTypeCompleteLocalDeformation` of
`MultiplicativeTypeCompleteLocalDeformationStatement`
([`MultiplicativeTypeCompleteLocalDeformationProof`](MultiplicativeTypeCompleteLocalDeformationProof.md)),
using the nilpotent diagonalizable models and the published split adic Hom
comparison.

Let `A` be a complete local noetherian commutative ring, `H` a diagonalizable
group scheme over `Spec A`, and `G` an affine flat group scheme whose actual
special fibre is diagonalizable. The theorem
`specialFibre_hom_bijective_of_diagonalizable` says that actual restriction
of group-scheme homomorphisms to the special fibres is bijective. The target
need not be locally of finite type for this comparison.

`formal_first_bijective` shows that a compatible formal Hom system is
determined by its first term whenever successive restriction maps are
bijective. Injectivity is induction using compatibility; surjectivity uses
the published recursive construction of a system from stepwise surjectivity.
The actual nilpotent diagonalizable models from LocalAdicDiagonalizableModels
make every successive restriction bijective by local-ring character duality.

`specialFibre_hom_bijective_of_adicComparison` combines that formal comparison
with an explicitly supplied adic restriction bijection. Its first term is
over `A / m^(0+1)`. An explicit map from the actual residue-field test scheme
to this first quotient test and the evaluation/base-change identity identify
the resulting bijection with actual special-fibre restriction. This avoids
substituting equal rings inside dependent Hom types.

The unconditional split theorem applies the published
`HomScheme.AdicDiagonalizable.restrict_bijective_of_isDiagonalizable`, whose
hypotheses are adic completeness, a noetherian base, a diagonalizable source
and an affine target. Target flatness is used in the nilpotent models,
not in that adic-effectivity input.

`specialFibre_hom_bijective_of_splitCover` additionally packages the ring,
flatness and affinity interfaces for a finite local splitting cover of a
complete local noetherian base. It assumes an explicit descent-existence
input and combines it with the split-case bijection and fpqc faithfulness.
The main complete-local proof supplies that input from CoverDescent; the
split-cover helper itself does not assert descent without this hypothesis.

This is derived assembly of actual group-scheme comparisons for the Hom
lifting part of Conrad's Theorem B.3.2(2). No new algebraization premise is
assumed by the unconditional split theorem.
