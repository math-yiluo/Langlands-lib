# Quotient separation over original-chart domain covers

This internal construction compares original full strong maps between saturated
affinoid atlas presentations. Local equality in the actual source-subatlas
quotient, over a quasinet cover by original-chart domains, produces a global
refining source selection on which the complete strong maps agree.

The field, space, chart index and cover index have independent universes.
All domains use their actual induced subspace topology and contained original
charts. The construction concerns original strong maps; extending separation
to arbitrary quotient arrows and proving existence of glued arrows remain
separate obligations.

## Provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.3.1 on printed p.23 (PDF p.20), Proposition 1.3.2 on printed p.24
(PDF p.21), and the G-topology paragraph on printed p.25 (PDF p.22) motivate
the domain-cover morphism descent. The registered original source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
This is derived infrastructure in the original-chart model, with no claim of
full Proposition 1.3.2 or identification with all analytic domains in a
maximal finite-gluing atlas.

## Construction and proof

`refiningSubatlasInclusion_comp_eq_restrictSubatlasSource` identifies categorical
source restriction with the literal source restriction of a full strong map.
The saturated composition formula computes pullbacks through each chart's
own original index. The intervening bounded restriction is the identity,
which proves equality of complete bounded algebra homomorphisms.

`strongFunctor_map_eq_iff_exists_refiningRestriction` uses the exact
source-quotient equality criterion. Restricting the top-selection
representatives to a common selection and composing the inclusion diamond
produces equality of literal source restrictions. Conversely, any such full
equality gives the same quotient class.

`StrongLocallyEqualOnDomains f g D` records quotient equality of the actual
restrictions of `f` and `g` to every `D k`. The proved equality criterion
supplies each `domainEqualityLocalSelection`, together with equality of
the complete local source restrictions. `domainCoverEqualitySelection`
assembles these into a global refining selection using
`coverRefiningSelection`. This construction retains the covering member,
the original source chart and its selected local copy.

The cover condition gives, at every point, finite covering members whose
union is a neighborhood. Consequently each point belongs to some member.
The corresponding local equality proves equality of the actual continuous
maps. For every globally selected chart, its retained local witness gives
equality of each bounded pullback to every admissible target chart, using
independent admissibility proofs. Strong-map extensionality proves
`domainCoverEqualitySelection_eq`. Applying the quotient equality criterion
gives `strongFunctor_map_eq_of_domainCover`.

No injectivity of restriction maps, faithfulness of the quotient functor,
or recovery of bounded algebra maps from spectrum-point values is assumed.
No whole original source chart is required to lie in a covering member.
Empty spaces and covers are allowed whenever the stated cover condition holds.
