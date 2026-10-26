# Complex determinant characters under actual Levi conjugation

Author: Worker 429.

`Langlands.LeviComplexPowerConjugationStatement.{uF,uV}` is a closed
proposition definition. It asks for compatibility of the published complex
product-Levi character and twist with the published, actual Levi conjugation.
This module states the compatibility; it contains no proof of it.

Fix an actual p-adic field `F`, a compatible realization `T`, two ordered block
shapes `B` and `C` of the same rank, and an actual coordinate permutation `w`
with `hw : CuspidalSupport.ConjugatesLevi B C w`. The published
`CuspidalSupport.blockEquiv hw` is a bijection `e` from the source block labels
to the target block labels. It sends source block `i` to the block containing
the images under `w` of all its coordinates. The sizes of corresponding blocks
agree. Set

`zC(j) = z(e.symm(j))`.

The first conjunct is equality of actual group characters on the target
product Levi:

`(T.leviComplexPowerCharacter B z).comp (leviConjugation B C w hw).symm`
`= T.leviComplexPowerCharacter C zC`.

Here composition uses the inverse conjugation's underlying monoid homomorphism.
At a target element `m`, the source character is evaluated on its actual inverse
Levi conjugate. This convention explains why the exponent at target block `j`
comes from source block `e.symm(j)`.

The second conjunct universally quantifies every complex module `V` in its
independent universe and every representation `ρ` of the source product Levi.
Transporting the source complex twist equals the target complex twist of the
transported representation. Both sides act on the original `V`; transport is
the existing inverse-conjugation precomposition, and twisting is the existing
scalar action by the actual determinant character. The assertion is equality
of representations, not merely existence of an intertwining equivalence.

All complex determinant parameters are allowed. No rank positivity, minimality
of `w`, irreducibility, admissibility, smoothness, temperedness, support, chamber,
zero-sum or tensor-factorization assumption is imposed. Rank zero and the
one-block case remain included. The topology enters only through the existing
normalized determinant character; no analytic or measure hypothesis is added.
The field and representation-carrier universes remain independent.

This is an internal algebraic compatibility statement. The published
`MinimalWeylTransportProof` supplies `blockEquiv`, `innerMap_bijective`,
`index_innerMap` and the equality of corresponding block sizes for every
conjugating permutation. These facts do not require the minimality assumption
used by some later lemmas in that module. Reindexing both matrix coordinates
identifies the determinant of each block of the inverse conjugate with the
determinant of its corresponding target block. Determinant invariance under
simultaneous reindexing and reindexing the finite product then give the proposed
character equality. Unfolding the existing scalar twist and inverse-conjugation
transport gives the proposed representation equality. This paragraph explains
the provenance and intended separate proof; it does not claim an implemented
proof in this module.

This compatibility is independent of any induced-family packaging. It does not
identify a consumer's separately supplied equality of flattened shapes or
refined-subgroup equivalence. It asserts no Jacquet occurrence, branch selection,
analytic continuation, cone bound, multiplicity equality, quotient extraction
or classification theorem.
