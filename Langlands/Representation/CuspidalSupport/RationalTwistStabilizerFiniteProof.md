# Finite unramified twist stabilizers

Worker 137. This module proves the exact published proposition
`Langlands.CuspidalSupport.RationalTwistStabilizerFiniteStatement`
with independent universes `uF` and `uV`.

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, V.2.7, printed p.109 / PDF p.115,
registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 137 read PDF pp.113–115, including the finite-index input in V.2.6.
No project errata note for this source was found.

The implemented proof uses the full centre instead of choosing the source's
uniformizer lift inside the split centre. The published
`rationalCommonNormKernel_sup_center_finiteIndex` proves that the common
rational-character norm kernel joined with the full centre has finite index.
The published `finite_centralTrivialUnramifiedCharacters` therefore makes
the kernel of restriction of unramified characters to the centre finite.
Concretely, a character in this kernel descends to the displayed finite
quotient; its values are roots of unity of bounded order, so only finitely
many such characters exist.

For a character stabilizing the given representation, fix a central element.
Its action is an intertwining endomorphism, hence a scalar by
`Schur.rationalPoint_scalarEndomorphism`. This scalar is nonzero because
the group element acts invertibly on a nonzero representation. Apply the
given twist isomorphism to its action on a nonzero vector. Linearity,
intertwining, and cancellation force the twisting character to have value
one on the central element. Thus the stabilizer lies in the finite
restriction kernel.

The scalar Schur theorem applies to every irreducible smooth representation
on the actual rational-point group, using its canonical topology and countable
dimension. The argument adds no admissibility hypothesis. The statement and
all its imported files remain unchanged.
