# Actual integer-ring diagrams for arithmetic spreads

Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.6, Remark 3.5 and the discussion of (3.5.1), uses the
outside-S integer rings as a filtered system with colimit the global field.
This module constructs that system and its canonical field-valued cocone
over any fixed initial integer ring. The colimit property is a separate
statement and proof obligation.

For the actual discrete curve places, `curvePlaceSIntegersOverDiagram k F S`
has the existing actual `curvePlaceSIntegers k F T.val` at a finite set T
containing S. Its scalar action is the literal inclusion from the original
outside-S integer ring. `curvePlaceSIntegersOverMap` uses the existing
integer inclusions. The cocone `curvePlaceSIntegersOverCocone` has point
`curvePlaceFieldOver`, whose underlying ring is F, and its component at T
is the integer subring's actual inclusion into F. The component formula
`curvePlaceSIntegersOverι_apply` is definitional.

For number fields, `numberFieldSIntegersOverDiagram K S`,
`numberFieldSIntegersOverMap`, `numberFieldOver`,
`numberFieldSIntegersOverι` and `numberFieldSIntegersOverCocone` give the
same constructions using Mathlib's original S-integer subalgebras of K.
The formula `numberFieldSIntegersOverι_apply` identifies each component
with the actual subring inclusion.

Both diagrams use the existing filtered index `AdelicLevelIndexAbove S`.
Naturality, identities and composition are the literal inclusion laws.
The algebra structure on each cocone point is the original inclusion of
the initial integer ring into the field, without an auxiliary field
presentation or replacement scalar action.

These are algebraic constructions: the integer rings and fields carry no
asserted topological colimit here. S may be empty and the common universe
is arbitrary. The curve-place definitions work for arbitrary fields k and
F with a k-algebra structure. This wider construction scope does not
assert that those arbitrary data form a global function field, that its
elements have finitely many poles, or that the displayed cocone is always
a colimit. Those hypotheses belong to the subsequent colimit target.
No model existence, generic-fiber identification or model independence is
proved by these definitions alone.
