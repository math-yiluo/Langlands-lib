# The natural p-adic scalar action on a p-divisible group

The short exact sequence at level zero forces its affine points to be
the identity point. The scalar factorization through this level then
shows that the `n`-th actual finite group scheme is killed by `p^n`.
`levelZModAction` gives the induced action of `ℤ/p^nℤ` by scheme
endomorphisms.

`padicAction` applies `PadicInt.toZModPow` at each level. One integer
representative of the residue at a larger level gives the same scalar
on any smaller level, so both tower arrows commute with the action.
Every morphism of the towers commutes with these scalars. Postcomposition
by the target scalar therefore makes the category linear over `ℤ_p`.

The construction derives the natural scalar action from Tate 1967,
§2.1, sequence (2), printed p. 161 (PDF p. 2). The action by residues at
the finite levels gives the same scalar convention as the action on
points in §2.4, printed p. 167 (PDF p. 5).
