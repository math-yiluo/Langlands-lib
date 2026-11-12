# Finiteness of Henniart's candidate sets with p-adic Bernstein–Zelevinsky finiteness

Author: Worker 4803. Module `Langlands.Correspondence.HenniartPadicConductorFinitenessProof`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields) and `uV`
(supercuspidal carriers), independent.

## Statement: `SupercuspidalEpsilonConductorFinitenessPadicReductionStatement.{uK, uV}`

The implication

`RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} →
Conductor.ConductorExponentStatement.{uK, uV} →
SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV}`,

proved as `supercuspidalEpsilonConductorFinitenessPadicReduction` from the theorem
`supercuspidalEpsilonConductorFiniteness_of_pairEpsilon`.

The conclusion is the published component of `HenniartStableMapStatement`: for a
nontrivial additive character `ψ` of a p-adic field `K`, a measure `ν` self-dual for
`ψ`, a rank `k + 1`, a character `ω` of `Kˣ` and an integer `m`, only finitely many
supercuspidal classes `π` of `GL_(k+1)(K)` have central character `ω` and an epsilon
factor `c q^(-ms)` against the trivial character of `GL_1(K)`. The two hypotheses
are the published Bushnell–Henniart–Kutzko and JPSS statements described in
`HenniartConductorFinitenessProof.md`; the theorem asserts neither.

It is the published `SupercuspidalEpsilonConductorFinitenessReductionStatement`
(module `HenniartConductorFinitenessProof`) without its first hypothesis,
`Henniart.SupercuspidalBoundedLevelFinitenessStatement.{uK, uV}` (bounded-level
finiteness over every nonarchimedean local field). The other two hypotheses and the
conclusion are unchanged.

## Provenance

Internal, derived. Henniart (2000), §4.3, printed p. 452 (PDF p. 14): the central
character and the conductor of the candidates are fixed, so "il n'y a donc qu'un
ensemble fini `P` de possibilités". The sources of the published reduction are
listed in `HenniartConductorFinitenessProof.md`. The removed hypothesis is
Bernstein and Zelevinsky (1976), Corollary 4.15, printed p. 41, whose p-adic case is
proved in the supporting module `PadicSupercuspidalFinitenessProof`.

## Proof

`supercuspidalEpsilonConductorFiniteness_of_pairEpsilon` repeats the proof of the
published `supercuspidalEpsilonConductorFiniteness_of_conductor` line by line, with
one change. The scalar matrices give `e : Kˣ ≃* Z(GL_(k+1)(K))`; put
`χ = ω ∘ e⁻¹` and `b = (m - (k+1) n(ψ)).toNat`. The candidate set is contained in
`SupercuspidalClass.centralLevelStratum χ b`. The published proof takes the
finiteness of that stratum from its bounded-level hypothesis at the field
`K.Carrier`. Here it comes from
`CompactOpenFiniteness.centralLevelStratum_finite K k χ b` (module
`PadicSupercuspidalFinitenessProof`), which holds with no hypothesis. The inclusion
is proved as before. For a member `π` with representative `A`, `A` has central
character `χ` by `supercuspidalCentralActsBy_iff`. By the published
`exists_newvectorConductor_of_pairEpsilon`, `A` has newvector conductor
`b' = m - (k+1) n(ψ)`, so `b = b'` and the first fixed level of `A` is at most `b`
(`Conductor.firstFixedLevel_le_iff`).

`supercuspidalEpsilonConductorFinitenessPadicReduction` is that theorem as a term of
the statement. Standard axioms only.
