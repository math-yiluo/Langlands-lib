# The first actual E6 weight and its branch-kernel restriction

This internal construction specializes the published actual kernel comparison
and integral-weight restriction to an E6 numbering whose distinguished set is
exactly zero-based vertex 1. It gives an explicit ordered A5 numbering, retaining
the first weight at zero-based vertex 0. It introduces no literature claim or
Tits obstruction.

`e6Branch_zero_iff` rewrites the exact distinguished-set hypothesis: a simple
vertex is a zero vertex precisely when its E6 number differs from 1.
`e6BranchZeroNumbering` uses the actual ambient numbering and `finSuccAboveEquiv`
to number the actual zero vertices in the order `0,2,3,4,5`.
`e6BranchZeroNumbering_ambient` recovers the original number by inserting the
omitted vertex with `Fin.succAbove`.

`KernelComparison.e6BranchNumbering` composes that numbering with the actual
kernel vertex equivalence. Its ambient-number formula follows from the same
formula on zero vertices. Its Cartan formula uses preservation of every ordered
Cartan entry by the actual comparison and checks the finite E6 submatrix
against the full A5 matrix.

`KernelComparison.weightRestriction_e6_firstWeight` states an equality of actual
integral characters after separable-closure base change. The restriction map
is the published precomposition map along the actual compatible torus
morphism. Both integral coroot spans are explicitly required to be the full
cocharacter lattices. The first weight is the published
`TypeANegationWeyl.firstWeight`, whose definition and pairing identity are
generic and do not require a type A Cartan hypothesis. Equality is tested
against every actual simple kernel coroot. Adjointness of character
restriction gives the ambient first-weight pairing. Inserting vertex 1
preserves the predicate of having number 0, so this equals the corresponding
kernel first-weight pairing. The full kernel coroot span implies equality.

`anisotropicKernel_weightRestriction_e6_firstWeight` specializes this equality
to the particular `d.anisotropicKernelIndex` selected by the supplied actual
index. Simple connectedness of the ambient group supplies both required
coroot-span equalities, using the published simple connectedness of its actual
anisotropic kernel. No absolute almost-simplicity, split-rank, full-star or
field-characteristic restriction is needed for these character identities.

This module supplies the numbering and character identity needed to combine
the ambient E6 first-weight calculation with a future actual kernel obstruction
comparison and a norm-one normalization. It constructs no obstruction map,
compares no Brauer classes, and proves no centre-moving automorphism.
