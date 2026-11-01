# Quotient idempotence and the fixed-part quotient comparison

This module states the quotient-idempotence lemma and the fixed-part quotient
comparison of David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated **9 July 2026**, I.3.2, printed pages 20–21 / PDF pages 26–27.
The registered governing original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Those pages, the conventions on printed page 6 / PDF page 12, and the
definition of the corner functor on printed page 19 / PDF page 25 were read.
The 2020 edition is not used.

The registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
was read on PDF pages 1–2. Its I.3.2 corrections treat tensor injection and
the later simple-module argument; the governing 2026 text includes the
balanced-map argument and the maximal-kernel argument. This unit states neither
of those results. No separate project errata file for these sources was found.

All declarations are in `Langlands.Algebra`. They are definitions returning
`Prop`, with no proofs of the comparison assertions. Worker 1151 authored
the Lean and Markdown; Worker 6 supplied the task's passage analysis and
the elementary ambient-generalization argument described below.

## Published constructions and scope

Let `A : Type uA` be an arbitrary associative `NonUnitalRing`, possibly
noncommutative, and let `e : Idempotent A`. Let `M : Type uM` be an additive
commutative group with its specified original `NonUnitalModule A M`.
There is no ambient identity-action law, even when the ring happens to
have a unit. The targets require neither `IsIdempotented A` nor
`IsNondegenerate A M`, and impose no nontriviality condition.

The imports use the actual published constructions:

| Notation here | Lean construction |
| --- | --- |
| \(F(M)\) | `NonUnitalSubmodule.idempotentAnnihilator e M` |
| \(Q(M)\) | `annihilatorQuotientCarrier e M` |
| \(q_M\) | `annihilatorQuotientProjection e M` |
| \(Q(f)\) | `NonUnitalModuleHom.annihilatorQuotientMap e f` |
| \(J(M)\) | `NonUnitalModuleCorner.FixedPart e M` |
| \(J(f)\) | `NonUnitalModuleCorner.restrict e f` |

The module imports `IdempotentAnnihilatorQuotient.NamedCarrier` directly;
it does not identify its carrier with the other reviewed `ExplicitAction`
interface. The quotient's additive group and original action are explicitly
installed using `annihilatorQuotientAddCommGroup` and
`annihilatorQuotientModule`, including the iterated quotients. The corner
ring, fixed-part groups and actions are explicitly installed using
`Idempotent.Corner.ring`, `fixedPartAddCommGroup` and `fixedPartModule`.
The local names in the targets abbreviate these existing objects and maps;
they create no replacement quotient, fixed part or functor.

The ring universe `uA`, pointwise carrier universes `uM` and `uN`,
and categorical carrier universe `uC` are independent. Each natural
isomorphism uses a single fixed carrier universe `uC`. The pointwise
naturality targets retain independent source and target universes.

## Quotient idempotence

`IdempotentAnnihilatorQuotientIdempotence e M` asserts all of the following:

1. Every element of \(F(Q(M))\) is zero.
2. The actual \(q_{Q(M)}:Q(M)\to Q(Q(M))\) is bijective.
3. There exists an original `A`-linear map
   \(r_M:Q(Q(M))\to Q(M)\) such that
   \(r_M\circ q_{Q(M)}=\mathrm{id}_{Q(M)}\) and
   \(q_{Q(M)}\circ r_M=\mathrm{id}_{Q(Q(M))}\).
4. The entire induced map \(Q(q_M)\) equals the actual \(q_{Q(M)}\).

The third assertion quantifies existentially over the inverse; bijectivity,
annihilator vanishing and the inverse are conclusions, not inputs.
The source's displayed equality \((M_e)_e=M_e\), immediately after the
quotient definition on printed page 20, is represented by this canonical
invertible projection between distinct Lean types.

`IdempotentAnnihilatorQuotientIdempotenceNaturality e M N` includes
the preceding comparison assertions for both `M` and `N` and asserts, for
every original intertwiner \(f:M\to N\), the whole-map identity

\[
 Q(Q(f))\circ q_{Q(M)}=q_{Q(N)}\circ Q(f).
\]

For every pair of original-linear inverses satisfying both inverse
identities, it also asserts

\[
 Q(f)\circ r_M=r_N\circ Q(Q(f)).
\]

Existence of these inverses is part of the same closed target, through its
two comparison conjuncts. The conditional quantification expresses
independence of the choice of inverse.

`IdempotentAnnihilatorQuotientIdempotenceNaturalIso e` asserts the
existence of a natural isomorphism \(E:Q\simeq Q\mathbin{\ggg}Q\), for
the actual `NonUnitalModuleCat.annihilatorQuotientFunctor`. Its entire
forward natural transformation equals the left whiskering of the actual
`annihilatorQuotientπ` by `Q`. Thus its component at `M` is exactly
\(q_{Q(M)}\).

It also asserts the analogous natural isomorphism for the actual
`nondegenerateAnnihilatorQuotientFunctor`, using
`nondegenerateAnnihilatorQuotientπ`. After the published
`nondegenerateInclusion`, both its forward and inverse transformations
equal the restrictions of the ambient ones. These are equalities of entire
natural transformations; the existing functor definitions identify the
endpoints.

`IdempotentAnnihilatorQuotientIdempotenceTheorem` is the closed target for
this family. It universally quantifies the ring, its structure, the
idempotent and all pointwise carriers, and includes the categorical
assertion at the independent universe `uC`.

## Fixed-part comparison

`IdempotentAnnihilatorFixedPartComparison e M` asserts that the actual
corner-linear map

\[
 j_M=J(q_M):J(M)\longrightarrow J(Q(M))
\]

is bijective. It asserts that a corner-linear inverse \(s_M\) exists,
with both whole-map identities
\(s_M\circ j_M=\mathrm{id}_{J(M)}\) and
\(j_M\circ s_M=\mathrm{id}_{J(Q(M))}\).
It also asserts the existence of a corner-linear equivalence whose entire
forward linear map is precisely
`NonUnitalModuleCorner.restrict e (annihilatorQuotientProjection e M)`
and whose inverse linear map is \(s_M\).

`IdempotentAnnihilatorFixedPartComparisonNaturality e M N` includes
these existence assertions at both objects. For every original
intertwiner \(f:M\to N\), it asserts

\[
 J(Q(f))\circ j_M=j_N\circ J(f).
\]

For every pair of corner-linear inverses satisfying both inverse
identities, it asserts

\[
 J(f)\circ s_M=s_N\circ J(Q(f)).
\]

Every equality here is an equality of complete linear maps, not a
condition on chosen vectors or generators.

`IdempotentAnnihilatorFixedPartComparisonNaturalIso e` asserts the
existence of a natural isomorphism \(J\simeq Q\mathbin{\ggg}J\).
It uses the actual `NonUnitalModuleCorner.functor` and actual quotient
functor. Its entire forward transformation is the right whiskering of
`annihilatorQuotientπ` by `J`, so its component is exactly \(J(q_M)\).
The target also asserts the natural isomorphism between the actual
`NonUnitalModuleCorner.nondegenerateFunctor` and its composition after
the actual nondegenerate quotient functor. Its specified forward map uses
the actual nondegenerate projection. Both directions equal the ambient
transformations restricted along `nondegenerateInclusion`.

`IdempotentAnnihilatorFixedPartComparisonTheorem` universally closes
this family, with the same independent universe convention as the
quotient-idempotence target.

`IdempotentAnnihilatorComparisonsTheorem` conjoins the two closed family
targets for review of this statement unit. Their separate names remain
available for independent exact-proof successors after publication.

## Source correspondence and internal strengthening

The quotient-idempotence target records the unnumbered lemma on printed
page 20 / PDF page 26. The fixed-part comparison records the argument
on printed page 21 / PDF page 27 that the image under \(j_e\) of the
canonical quotient projection is an isomorphism, displayed as (I.3.2.2).
That displayed map has the induced module as its source. The ambient
statement here specializes to that map once the separate actual induced
module construction is available. No tensor induction is a premise.

The arbitrary-ring and arbitrary-original-action scope is derived internal
content. For quotient idempotence, if \(q_M(m)\) is killed by `eA`, each
\((ea)m\) belongs to \(F(M)\) and hence is killed by \(e\). Since
\(e(ea)=ea\), this implies \(m\in F(M)\), so \(q_M(m)=0\).
For the fixed-part comparison, an `e`-fixed vector in \(F(M)\) is zero.
If \(q_M(m)\) is `e`-fixed, then \(q_M(em)=e q_M(m)=q_M(m)\), giving
a fixed representative directly. These observations justify stating
the ambient strengthenings without exactness, local units or
nondegeneracy. They are provenance explanations, not Lean proofs.
Whole-map naturality and natural-isomorphism packaging are further
internal strengthenings using the actual published functors.

The targets cover the zero idempotent, zero original action and zero
carrier because all these choices are included in their universal
quantification. In the first two cases the existing quotient is
subsingleton and both fixed parts are zero; the comparisons remain
invertible between these zero objects.

Restriction to nondegenerate modules recovers the source's underlying
additive-action assertions. A correspondence respecting the source's
additional complex scalar structures remains a separate parent
obligation. The module supplies neither that correspondence nor
(I.3.2.1), generatedness, the simple-class bijection, the later equivalence,
or any proof of the comparison targets.

The final Lean examples check every target's complete unapplied signature
and `Prop` result, retaining the named action inputs and all intended
universes. Unequal ring/source/target universe assignments also check that
no hidden universe equality or inequality is required.
