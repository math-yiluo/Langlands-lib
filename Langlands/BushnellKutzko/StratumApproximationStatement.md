# Approximation of pure strata (T7)

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Theorem (2.4.1),
printed p. 65, and defining sequences (2.4.2), printed pp. 65–66
(PDF pp. 77–78).

`StratumApproximationStatement` is an unproved proposition definition
for every nonarchimedean local field `F` and finite-dimensional
`F`-vector space `V`, in independent universes. It is the conjunction
of the following source assertions.

For (2.4.1)(i), every pure `S` has an equivalent simple `T` with
the same chain and integers `n,r`. For every such simple `T`,
its generated-field ramification index and residue degree divide
those of `S`. Finally, for every pure `T` equivalent to `S`,
with these same order and integer parameters, simplicity is
equivalent to the assertion that its generated-field degree is
at most the degree of every pure `U` in that equivalence class.
The degree is `elementDegree F`, the dimension of the actual
generated algebra. This states minimal degree as an attained
minimum, with both implications.

For (2.4.1)(ii)(c), any equivalent simple `S,T` with the same
chain and parameters, and every tame corestriction `s` relative
to `F[S.b]/F`, admit an element `δ` of that actual generated
field with

`s(S.b−T.b) − δ ∈ 𝔓^{1−r}`.

Restriction of scalars embeds the value of `s` in the ambient
endomorphism algebra, and the published `subfieldEmbedding`
embeds `δ` there, so the difference is in the correct space.
The field structure is obtained from any witness that the
generated algebra is a field; such witnesses exist by purity.
Parts (ii)(a),(b) are already the critical-exponent and
ramification/residue-degree equalities in T5 and are not repeated.

For (2.4.1)(iii), if `S` is pure at its critical depth
`r = −k₀(S.b,𝔄)` and `T` is a simple equivalent with the same
parameters, then `T.HasSimpleDerivedStratum (S.b−T.b)`.
The critical-depth equality is expressed as `k₀ = −r` in
`WithBot ℤ`, with no extra finiteness assumption. The conclusion
quantifies every tame corestriction for the actual field
`F[T.b]`, and existentially supplies the derived stratum
`[𝔅_T,r,r−1,s(S.b−T.b)]` and an equivalent simple stratum
over that field. These are actual strata in `End_{F[T.b]}(V)`,
with the ring of integers constructed by integral closure,
using the original underlying lattice sets.

Finally, every pure stratum admits a finite family satisfying
`Stratum.IsDefiningSequence`, including all six conditions of
(2.4.2). This existence is a conclusion, not a field of the
original stratum or a premise.

The common-chain equations express the source's common hereditary
order using one fixed lattice-chain presentation. The source
specifies the same order and integers for the strata in these
parts; no structural, divisibility, exactness or approximation
conclusion is required as an extra hypothesis.
