# Residual Iwahori multiplication and finite generation

This internal supporting construction continues the finite residual-coset
argument in Renard, *Représentations des groupes réductifs p-adiques* (2026),
V.5.3, printed pages 124–125 / PDF pages 130–131. It does not assert an
actual reductive Cartan decomposition or the host uniform-support proposition.

`iwahoriLowerConjugate L a` is the genuine subgroup `a⁻¹ L a`.
For an orthant monoid homomorphism whose elements contract `L` backward,
these conjugates form an antitone family.

The double-coset lemma assumes an ordered lower-middle-upper factorization
of the compact open subgroup. Factor the inverse of the intervening level
element. Forward upper and middle preservation move these two inverse
factors to the left. Equality of the actual residual coset sets for the
lower conjugates at `b` and `a b` replaces the remaining lower factor by
one at `a b`, up to a final level element. This constructs literal
witnesses for `a K (b f) ⊆ K (a b f) K`. In particular, middle forward
preservation is an explicit hypothesis; it is not inferred from backward
preservation.

The existing `massIndicator_mul` theorem then gives the exact product of
mass-one Hecke indicators. The residual `f` is arbitrary and need not
normalize the level or commute with any positive generator.

For a homomorphism from a finite positive orthant into the group, the
positive-monoid conditions imply that all the lower conjugates lie in the
level and decrease with the orthant index. The published finite residual
coset frontier therefore gives a finite set `S` such that for every `n`
there is `m ∈ S`, `m ≤ n`, and
`massIndicator(e(n−m)) * massIndicator(e(m) f) = massIndicator(e(n) f)`.
The finite set is chosen before `n` and before any representation. It may
depend on the fixed residual `f`. This is a finite residual factorization,
not an assertion that the residuals belong to a commuting positive monoid.
