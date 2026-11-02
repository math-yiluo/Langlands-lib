# Transport of the finite action equations

Author: Worker 706.

This internal helper derives naturality and a pullback criterion for the finite
action equations from the scheme fibre product universal property. It uses the
existing relation unit and composition and does not assume approximation.
Its intended application is the descent of chart actions in the proof of
Stacks Project Proposition 70.8.1, Tag 07SU, registered as
`stacks-noetherian-approximation-2026-11-01`.

Fix a cartesian relation morphism `h : E → F`, with object map `f` and arrow
map `g`, and maps `p : P → E.U`, `q : Q → F.U`, `k : P → Q` satisfying
`p ≫ f = k ≫ q`. All schemes retain arbitrary universe `u`.

`unitInput p` inserts the identity arrow at a point of `P`; its two projection
lemmas give `p ≫ E.unit` and the identity. `unitInput_arrowMap` states that
the induced action-arrow map preserves this input. The proof uses preservation
of relation units and equality of the two fibre product projections.

`composableMap` sends the universal composable triple `(r,s,v)` to
`(g(r),g(s),k(v))`. Its three projection lemmas recover these components.
The compatibility equations follow from endpoint preservation and the square
on `p,q,k,f`.

For any two prospective action maps `a,b` satisfying
`a ≫ k = arrowMap ≫ b`, `evaluation_naturality` proves compatibility on
every scheme-valued compatible arrow and point by comparing the fibre product
inputs. `unit_equation_naturality` applies this compatibility to the unit
input. If the maps satisfy their target equations, `successive_naturality`
compares the two successive evaluations on universal composable triples.
`composite_naturality` compares evaluation by their composite, using
preservation of relation composition. None of these assertions assumes
the action unit or associative laws.

`successive_over` and `composite_over` show that the two universal expressions
lie over the target of the outer relation arrow.
`unit_equation_over` shows that the unit expression lies over the same point
of `E.U` as the identity.

Finally, `ofEquationsAfterMap` assumes that the square with top map `k`,
left map `p`, right map `q`, and bottom map `f` is a pullback.
A prospective action map satisfying its target equation is then an action
provided its unit and universal associativity equations hold after
composition with `k`. Pullback uniqueness combines these equalities with
their equalities over `E.U` to recover the original two equations.
`ofAssociative` supplies the complete action. This is a criterion for laws
on supplied data; it does not assert existence of descended data.
