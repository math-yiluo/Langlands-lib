# Geometric connectedness and finite closed covers

`FiniteClosedGeometricallyConnectedCoverCriterion` is a derived statement target
for the last paragraph of the proof of Stacks Project Lemma 37.28.4 (055G), in
the registered source `stacks-fibre-constructibility-local-dimension-2026-11-04`,
retained `055C.html`. That paragraph uses an intersection chain of geometrically
irreducible covering pieces to deduce geometric connectedness of a fibre. The
present target isolates the closed-cover criterion and only needs the pieces
to be geometrically connected. It supports the geometric-connectedness input
to Conrad's Theorem 3.4(2).

For an arbitrary field `K`, an actual scheme morphism `f : X ⟶ Spec K`, and a
finite family of actual closed immersions `g i : Z i ⟶ X`, suppose their
underlying ranges cover `X` and every composite `g i ≫ f` is geometrically
connected. The statement says that `f` is geometrically connected if and only
if the actual nonempty intersections of these ranges connect all indices by
finite chains. `IntersectionChainConnected` also requires that the index type
be inhabited. Equal indices are permitted in the intersection relation. The
criterion thus includes the empty index type: coverage then forces `X` to be
empty, and both geometric connectedness and the inhabited-chain condition
are false.

The scheme and field universe `u` and the finite index universe `v` are
independent. Geometric connectedness has Mathlib's actual meaning: connectedness
of every scheme pullback along a morphism from a field spectrum, including
nonemptiness. The target has no finite-type, Noetherian, affine, separation,
properness, smoothness, flatness or field-perfection hypothesis. The family is
not required to be the family of maximal irreducible components. It concerns
the underlying scheme points, not just rational points.

The statement is derived from the finite closed connected-cover comparison,
stability of closed immersions under base change, and the invariance of actual
coverage and incidence under field extension. A proof is a separate obligation;
this file contains only its Prop-valued target. The target neither constructs
covering pieces in a family nor spreads their geometric connectedness or
irreducibility. Those steps and the general generic-constancy theorem remain
separate obligations.
