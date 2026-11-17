# Complete cone lifts on nonempty aligned source charts

This internal construction lifts a commuting complete compatible strong cone
on an actual aligned original source chart. It retains the independent field
and common space/index universes. Smallness of the full pair quotient and
domain saturation of the source and input atlases are explicit.

The full cone equality identifies the bounded composites into every
admissible original common base chart. `coneChartPullback` therefore uses
the actual affinoid pushout lift. A nonempty source spectrum gives a point
in that pushout spectrum, so its original pair chart range is nonempty and
indexes the domain-indexed local atlas. Empty source chart domains need not
be included in the subsequent local domain cover.

The selected domain index can choose a different representative pair for
the same literal range. `coneChartLift` composes the original bounded lift
with the actual range restriction to that representative and then applies
the complete original chart-source construction. No spectrum map is used
to identify bounded maps.

Both projection identities are equalities of entire compatible strong maps
on the source chart domain. The range-restriction chart-change theorems
identify the changed legs with the original pair's left and right legs. The
pushout lift identities give exactly the original cone pullbacks, and
the complete chart-source recovery/composition laws conclude equality.

Global domain-cover gluing and the etale conclusions remain
further work. No external statement is transcribed.
