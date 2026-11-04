# Haar normalization at a common ambient compact open

This derived construction implements the scale prescribed by J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d’après Harish-Chandra)*
(2003), I.1, printed p.240 / PDF page 6 (zero-based index 5),
DOI 10.1017/S1474748003000082. The source fixes
one special maximal compact subgroup and assigns every closed algebraic
subgroup left Haar measure with its intersection with that compact subgroup
of mass one. The original pages 240–242 were read directly. Here a compact
open subgroup is supplied; existence and the special/maximal properties
of the source subgroup remain separate application obligations.

The implementation reuses the published
`Langlands.RankinSelberg.normalizedCompactOpenHaar` constructor. It does
not construct a subgroup measure by restricting ambient Haar measure.
For a closed embedded continuous group homomorphism `ι : H →* G` and a
compact open `K` in `G`, `compactOpenPreimage` is `ι⁻¹(K)`. Its compactness
follows from the closed embedding, and its openness from continuity.
`compactOpenHaarAlong` is Haar measure on `H` normalized on this preimage.
It is regular and gives this exact original-element set mass one.

The closed-subgroup specialization is `subgroupCompactOpenHaar`. It
uses the subtype embedding of the closed subgroup and gives
`{u : U | (u : G) ∈ K}` mass one. The subgroup's own Borel measurable
structure is explicit.

Under local compactness of `G`,
`compactOpenHaarAlong_eq_of_mass_one` identifies every regular
left-invariant measure with the constructed measure whenever its mass
on this preimage is one. The proof transfers local compactness through
the closed embedding, applies regular Haar uniqueness, evaluates the
resulting scalar identity on the normalized set, and obtains scalar one.

`measurePreserving_compactOpenHaarAlong` treats two actual carriers
in independent universes, with closed embeddings `ι` and `κ` into the
same ambient group. A continuous group equivalence `e` satisfying
`κ (e h) = ι h` preserves their constructed measures exactly. The
pushforward is regular Haar. Its mass on `κ⁻¹(K)` is one because that
set pulls back to `ι⁻¹(K)`. The preceding uniqueness theorem then
identifies the measures. This applies to different nested subgroup
copies without any scalar renormalization.

Closedness does not assert unimodularity. Two separate lemmas establish
right invariance of the constructed measure, either from a supplied
regular two-sided Haar measure on the same carrier by regular Haar
uniqueness, or from a genuine cover of that carrier by compact open
subgroups via the published `compactOpenCoverUnimodularity` theorem.

No quotient measure is changed or selected in this module. Compatibility
of actual quotient measures with these prescribed subgroup scales,
literal local product geometry, general reductive realization of the
charts, convergence and rational continuation remain open application
obligations. This unit closes no whole-task Plancherel condition.
