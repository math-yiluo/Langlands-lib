# The identity Mackey constituent when `D` is contained in `E'`

This derived arithmetic identification supports the two induction-in-stages
interfaces in [HarrisProposition48MackeyTransportStatement](HarrisProposition48MackeyTransportStatement.md).
It uses the compositum and actual Mackey character from
[HarrisProposition48InductionData](HarrisProposition48InductionData.md).
The source is M. Harris, *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134 (1998), 177–210
(`harris-1998-local-langlands`), Proposition 4.8 proof, printed p. 202
(Mackey characters of the form `a(ξ) ∘ N`) and p. 203 (prime branch,
`E_{t-1} ⊆ E'`). The algebra equivalence and its compatibility lemmas are
internal to the formalization, not separate statements in Harris.

For `D ≤ Q.conjugateField 1`, `Proposition48Problem.identityMackeyEquiv`
first identifies `Q.E'` with the range of its identity-conjugate embedding
in `Q.L`, then uses `D ⊔ Q.conjugateField 1 = Q.conjugateField 1` to identify
that range with `Q.mackeyField D 1`. This is an algebra equivalence over
`Q.E`, with its compatibility with the given maps from `Q.E` made explicit
by `identityMackeyEquiv_algebraMap`.

For `identityMackeyEquiv_comap`, the second equivalence is the actual
inclusion of the range into the compositum. The proof compares inclusion
and transport on adeles. At an infinite place they use the same completion
map. At a finite place the places below agree because the two maps on
integer rings agree. The completion maps are continuous and agree on the
dense diagonally embedded field in that completion, so they agree there
as well. The two maps then agree on units and on idele classes. The
norm-of-inclusion power formula on idele classes has exponent one here:
the algebra map is bijective. Thus the norm composed with transport by
the second equivalence is the identity. Pulling back the actual Mackey
character along the composite consequently cancels both this norm and
the inverse transport on the range, giving `Q.ξ`.

The sole field-containment hypothesis is `D ≤ Q.conjugateField 1`;
neither a prime degree assumption nor an automorphic existence or
compatibility theorem is used.
