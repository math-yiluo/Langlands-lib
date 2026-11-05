# Finite-field quasi-splitness

`FiniteFieldQuasiSplitStatement.{u}` asserts that every connected reductive group
scheme over every finite field `k : Type u` is quasi-split, at arbitrary universe
`u`. The conclusion is the existing `IsQuasiSplit G`: it retains connected
reductivity and requires an actual group scheme `B` over `Spec k` with an inclusion
`B → G` that is Borel over `k` and remains Borel over the algebraic closure.
The hypotheses contain no supplied Borel, split torus, or cocharacter.

This is the reductive specialization of Milne, *Algebraic Groups*, corrected
2022 reprint, Proposition 17.99 and the following sentence, printed p.384
(one-based PDF p.395). The source is registered as
`milne-2022-algebraic-groups`; retained file
`J. S. Milne - Algebraic Groups- The Theory of Group Schemes of Finite Type over a Field (2022 corrected reprint).pdf`,
SHA-256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
Proposition 17.99 constructs a Borel over the finite ground field by conjugating
a geometric Borel using Lang's theorem. The statement here records only its
quasi-splitness consequence, not the additional Borel-pair conjugacy assertion.
The finite-field hypothesis is inherited from the subsection and its Frobenius
argument. The retained author errata dated 2026-11-04 contains no correction to
this proposition or its consequence.

This module states the proposition and supplies no proof. It is a substantial
prerequisite for the finite-field central-cocharacter solvability proof, separate
from the parabolic/cocharacter comparison and lifting through unipotent quotients.
