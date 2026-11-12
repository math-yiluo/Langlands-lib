# Induced inside-Levi cuspidal representations lie in `Alg({K})`

Worker 4195. This unit states one proposition and gives no proof. The proposition
is the step of Renard's proof of Théorème VI.7.2 that says each induced summand
of the finite cuspidal embedding is split. Here it is stated at the coarse level
of the support categories `Alg({K})`.

## Source

The registered original is David Renard, *Représentations des groupes réductifs
p-adiques*, version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof of Théorème VI.7.2 (printed pp. 182–183 / PDF pp. 188–189) first
embeds every smooth representation into a finite sum over the standard
parabolics `P = MN` of induced representations `i^G_P(ρ_M)`, with `ρ_M`
supercuspidal in `M`. It then shows that each `i^G_P(ρ_M)` is split according
to `Ω(G)`. The final paragraph of printed p. 183 argues as follows. If `(σ, E)`
is a composition factor of `i^G_P(W_D)`, then by exactness `r^G_P(σ, E)` is a
subquotient of `r^G_P i^G_P(W_D)`. By Lemme VI.5.3(iii) and (V.4.3.3), the latter
is filtered by the conjugates `w(W_D)`, `w ∈ N_G(M)/M`. So the cuspidal support
of `(σ, E)` lies in the component of `Ω(G)` determined by `D`.

Grouping the inertial classes `D` of one Levi together gives the coarse
assertion stated here. Every irreducible subquotient of `i^G_P(ρ)` has cuspidal
support of the form `(n M n⁻¹, Ad(n) σ₀)` with `σ₀` irreducible cuspidal in `M`.
The decomposition `W = ⊕_D W_D` and the commutation (VI.7.2.1) of induction with
infinite direct sums are not needed at this level.

## Lean statement

`InducedCuspidalSupportCategoryTarget` is stated over the generic standard
families `P M U` of `Langlands.Aubert.General`, with the same actual data as
`SupportCategoryDecompositionTarget`. These data are the semidirect
decompositions `h`, closed radicals `hU`, closed Levis `hM`, the standard
decompositions inside each Levi `hL`, and the association relation
`IsAssociate`. For every standard index `K` and every smooth complex
representation `τ` of `M K` with carrier in `Type (max uG uV)`, it asks the
following. If `τ` satisfies the published `IsLeviCuspidal` predicate, then the
actual normalized induction `(normalizedInductionFunctor (h K) (hU K)).obj τ`
satisfies the published `IsInSupportCategory` predicate for `K`. That predicate
is the erratum's `Alg({K})`: every irreducible subquotient is a subquotient of
`i^G_{L_J}(Ad(n) σ)` for some `n` with `IsAssociate K J n` and
`M J = n (M K) n⁻¹`, and some irreducible cuspidal `σ` of `M K`.

`τ` need not be irreducible, admissible, finitely generated or of finite length.
It may be zero. This generality is the one the embedding produces:
`FiniteCuspidalInducedEmbeddingTarget` supplies arbitrary inside-Levi cuspidal
`τ(K)`. The cuspidality predicate is exactly the published one: every normalized
Jacquet module along a proper standard parabolic of `M K` vanishes. Aubert's
*cuspidale* is Renard's *supercuspidale*.

`RationalInducedCuspidalSupportCategoryStatement.{u, v}` applies the generic
proposition at universes `.{u, u, max (u + 1) v}` to the actual standard
rational-point families. These are the families of a maximal split torus and a
generic cocharacter of an arbitrary connected reductive group scheme over a
nonarchimedean local field. The application uses the actual association
relation `rootAssociation i ν hN hZ`. The binder telescope is the same as in
`RationalSupportCategoryDecompositionStatement`. It keeps the standard
cocharacter, standard Levi-intersection, relative-root, normalizer and
centralizer comparison assertions. It also keeps closedness of the Levis and
radicals and the point-topology hypotheses. The representation carriers are in
`Type (max (u + 1) v)`, as in the other rational support targets.

## Provenance and use

The source states this step inside a proof at the finer level of inertial
classes. Its formulation through `IsInSupportCategory` and arbitrary
inside-Levi cuspidal `τ` is internal (derived). It is what the companion
reduction `rationalSupportCategoryDecomposition_of_inducedCuspidal` (in
`RationalSupportCategoryDecompositionReduction`) needs. The published
`CuspidalJacquetFactorExtractionTarget` assumes an irreducible inducing
representation, so it does not directly give this proposition for arbitrary
`τ`. Renard's argument suggests a proof. Let `π` be an irreducible subquotient
of `i_K(τ)`. Exactness of the Jacquet functor and the geometric-lemma
filtration of `r_J i_K(τ)` show that every irreducible cuspidal subquotient of
`r_J(π)` is a conjugate of a subquotient of `τ` along an association of `K`
with `J`. Frobenius reciprocity then gives the required cuspidal support.
