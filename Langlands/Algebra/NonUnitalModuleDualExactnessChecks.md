# Interface checks for actual nondegenerate dual exactness statements

This is an internal verification companion to
`NonUnitalModuleDualExactnessStatements.lean`, with the same source
and scope described in that file's Markdown. It contains no proof
of any dual-exactness proposition.

For each of the four principal targets, a complete unapplied `@` check
requires the declaration itself to have type `Prop`. Explicit equalities
to the full quantified proposition check each exact unfolding with `rfl`.
The categorical target is checked at arbitrary independent universes and
at `(uA,uM)=(0,1),(1,0)`. The original-map target is checked at arbitrary
four independent universes and at `(0,1,2,3),(3,2,1,0)`. Standalone
endpoint targets have the analogous three-universe checks.

Conditional examples apply each original-map target to `Aᵐᵒᵖ`,
checking the original right-module interpretation without supplying
complex modules on the carriers. Two equalities check that the named
abelian structures on the left and right original categories have the
inherited pointwise preadditive structures. An `Iff.rfl` check expands
the Renard contravariant sequence predicate into both one-sided exact
sequence conditions, with the mono and epi conclusions.

The final checks identify the whole actual right-to-left functor map
with `fromDoubleOppositeMap` of the opposite-ring pullback, and compare
their complete underlying functions. These are definitional checks of
the already published functor and transport; they explain why the
opposite-ring original-map interfaces also describe its transported
left maps.
