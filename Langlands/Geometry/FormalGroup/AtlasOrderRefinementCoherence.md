# Order-linear coherence for actual atlas refinements

This derived unit constructs formal order-linear isomorphisms comparing
direct with successive restriction and comparing different selected source
charts on an equal finer cover. Their evaluations identify the actual
full-family restriction maps.

## Source and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), paragraph immediately before section 2, permits formal groups
glued over localizations. These are internal coordinate constructions for
that convention, not separate numbered assertions of the article.
Registered source: `drinfeld-1976-coverings-p-adic-symmetric-regions`,
SHA256 `7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

The parameters are arbitrary commutative rings O and R with an O-algebra
structure on R, a possibly noncommutative O-algebra ring D, a finite
coordinate type in `Type`, and an actual atlas X carrying an actual formal
`OrderAction D X`. Refinements include actual principal covers, covering
equations, selected original charts and localization containment
witnesses. Covers may be infinite. Tests have the universe v of R and
full-family modules have universe v + 1.

## Direct and successive restriction

For q refining X and r refining `q.atlas`,
`compOrderChart_coordinates` identifies the actual order endomorphism
series obtained by direct restriction along `q.comp r` with those obtained
by successive restriction. The proof identifies both with the original
action extended directly to the test algebra, using
`orderChart_coordinates` three times.

`orderCompHom` and `orderCompInv` have underlying actual formal maps
`q.compHom r` and `q.compInv r`. Those maps have identity coordinates;
the preceding action-coordinate equality therefore proves that both
commute with every element of D. `orderCompIso` packages these maps and
the existing formal inverse equations as an actual order-linear formal
atlas isomorphism.

`orderComp_onPoints` states that this isomorphism carries direct
full-family restriction to successive full-family restriction. Its proof
is the existing evaluated square of those actual underlying formal maps.

## Source-chart choices

For q and r refining X with equal finer covers, `orderSourceHom` has
underlying actual formal map `q.sourceHom r h`. Its coordinate series are
the original transition from q's selected source chart to r's selected
source chart. The original order action commutes with that transition.
The action-coordinate comparison for each refinement identifies both
sides with the finer actions, proving formal order-linearity.

`orderSourceHom_id` and `orderSourceHom_comp` lift the existing formal
identity and composition equations by subtype extensionality.
`orderSourceIso` uses the two opposite source-choice comparisons and
these equations as its formal inverse laws. `orderSource_onPoints`
identifies the restrictions of every original complete family.

The resulting `OrderAction.Iso` objects have their existing natural
isomorphisms on coefficient-algebra and Nilp module functors. These
constructions give formal comparison data with specified maps. They do
not assert a canonical map from an unspecified isomorphism class, height
reflection, a framing construction or representability.
