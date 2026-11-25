# Opposite-pair independence of the canonical scalar

`conditionalDynamicOppositePairScalar` proves exactly
`Langlands.Plancherel.ConditionalDynamicOppositePairScalarStatement`. This is the
opposite-pair transport form of Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d’après Harish-Chandra)*, IV.3 (1), printed pp. 285–286; see
[the statement and its source notes](DynamicOppositePairScalar.md). The proof's
auxiliary lemmas are derived from the Library's canonical scalar construction,
not additional statements taken from the source.

## Identifying the subgroup and compact-picture data

The target's equality of centralizer functors gives `levi ψ = levi χ` by
`changeLevi_mem_iff` and subgroup extensionality. Rather than rewrite dependent
operators in place, `pairScalar_transport` takes the five subgroups of the
second scalar as variables and substitutes the Levi and the four parabolic and
radical equalities. In the common Levi, `leviChange` is the identity by
`leviChange_apply_coe` and extensionality. The pullback of `A` along its inverse
is then definitionally `A`, so the two inducing representations agree.

In each order the two scalars use the same Borel structures and the same
compact open `K`. The radical Haar measures are `subgroupCompactOpenHaar` at
`K`, the intersection measures are `sourceIntersectionHaar`, and each quotient
measure unfolds to `sourceQuotientMeasure` of the corresponding ordered pair
of radicals. Compact-open covers of the radicals come from compact-open
containment applied to singletons. After substitution, the constructions have
the same inputs up to proof irrelevance, including the covers used to choose
the quotient measures. Proof irrelevance also handles the decomposition,
closedness, unimodularity, Weil compatibility, squared-modulus and `G = P K`
proofs. Thus the compact pictures attached to matching decompositions are
literally the same; in the exchanged case the two pictures and the two ordered
measure inputs are exchanged together. No comparison up to a measure factor
is needed.

## Transport in a fixed order

Write `L = parameterScheme χ`, `L' = parameterScheme ψ`, and
`iso = parameterChangeIso χ ψ hM`. The compatibility
`parameterHomeomorph_parameterChangeIso` identifies the two parameter
homeomorphisms on the common Levi. If `R(z') = z' ∘ iso.hom` on characters
(using the map on rational points), `unramifiedCharactersHomeomorph_restrict`
shows that `z'` on the `L'` side and `R(z')` on the `L` side give the same
character of the Levi. The indexing families of norm characters may differ;
the twist, normalized induction and compact integral depend only on the
underlying character, as shown by the three congruence lemmas in
`ParameterValue`. Consequently the full-domain predicates correspond under
`R`, and the actual compact operators agree pointwise at corresponding
parameters. This uses the exact full domains, not just the supplied open
convergence subsets.

`continuationRestrict` transports each continuation by precomposing its
numerators and denominator with `R`. The full-domain and compact-operator
comparisons verify the continuation data on the second side. In
`continuedCompositeRationalScalar_transport`, continuation independence on
that side replaces the supplied continuations with the transported ones, using
the two given nonempty open convergence subsets **separately**. If `a/b`
presents the scalar coefficient of the continued composite on the first side,
the transported `a` and `b` present the second coefficient on the common
regular region. The rational-scalar presentation theorem identifies this
fraction with the computed scalar; the field equivalence sends `a/b` to
exactly that fraction.

`standardInductionCompositeCanonicalRationalScalar_transport` uses the
normalized vector and functional extracted at a point of the first
irreducibility locus. They can be used in the second compact carrier because
it is the same carrier. The canonical scalar's `eq_extraction` theorem on the
second side identifies its value with the fraction computed using this pair,
regardless of the independently supplied second irreducibility locus and
continuations. No equality or intersection of the supplied loci is required.

## Exchanging the order

When `P_G(ψ) = P̄`, the irreducibility locus of the induction from `P_G(ψ)`
is pulled back along the character transport `R⁻¹` to a nonempty open locus
on the `L` side for induction from `P̄`. The induction congruence proves
irreducibility there. With that locus and the original locus for `P`,
`standardInductionCompositeCanonicalRationalScalar_eq_reverse` identifies the
scalar of `J_{P|P̄} J_{P̄|P}` with the scalar of `J_{P̄|P} J_{P|P̄}` for the
same two compact families on the `L` side. The same-order transport then
applies with the directions reversed. This is the comparison of the two
orders of the same operators; it uses no composition formula for a third
parabolic or nonvanishing assumption for an intertwiner.

## Scope

The theorem imports the statement unchanged and uses only its hypotheses.
In particular the field characteristic and the field and inducing-carrier
universes remain unrestricted, `G` need not be split or quasisplit, and
`hRefl` and `hCST` are used as in the target's canonical scalar construction.
The proof neither supplies convergence, continuation or irreducibility data
nor compares the scalars for different opposite pairs or different choices
of `K`.
