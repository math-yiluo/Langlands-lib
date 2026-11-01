# Interfaces and boundaries of actual corner evaluation

This is an internal construction and interface companion to
`Langlands.Algebra.NonUnitalModuleCornerEvaluation`. Its provenance is the
actual original-action balanced pairing underlying Renard (9 July 2026),
I.3.2, printed pp.21–22 / PDF pp.27–28. The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These interface and boundary checks are internal consequences, not additional
assertions attributed to the source.

The first section assigns each public declaration of the construction module
in unapplied `@` form to its complete intended type. This checks parameter
order and the absence of extra inferred hypotheses for the pairing, its
balancing, actual quotient lift, original A-linearity, pure-tensor formula,
recovery and uniqueness, whole-intertwiner and additive-map naturality,
and both actual natural transformations with their component and inclusion
laws. `evaluationInterface` is the named entry declaration for these checks.
The original fixed subgroup has exactly its published inherited group and
`fixedPartModule`. The tensor has exactly `tensorAddCommGroup` and the original
residual `tensorModule` action.

Unequal-universe specializations cover a small ring with a larger module and
a larger ring with a small module. Naturality also has explicit specializations
with three distinct universes for ring, source and target. Both categorical
interfaces retain the carrier bound `max uA uM`; the specialization with
`uA = 1, uM = 0` therefore uses carrier universe 1.

The competing-action section introduces another original action on the same
ambient carrier, an unrelated right corner action, another ordinary fixed-part
corner action, another nonunital fixed-part action, and another action on the
same tensor carrier. It first verifies that inference sees those competing
instances. Explicitly supplying the original action to evaluation still gives
exactly the named source structures, the balanced quotient lift and the formula
for that supplied original action. The other instances cannot replace it.

The boundary section checks evaluation for zero idempotents, arbitrary
subsingleton ring or module carriers, a specified zero original action, and
the singleton module. It also checks a zero original action of the unital
ring of integers on its nonzero additive group, without imposing a unit law.
The zero-map equalities follow by pure-tensor uniqueness and the original
action laws. These are elementary construction checks; they assert no general
image, kernel, injectivity, surjectivity, equivalence or adjunction result.
