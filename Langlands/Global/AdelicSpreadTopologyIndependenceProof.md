# Independence of adelic point topologies from finite-type spreads

`adelicSpreadTopologyIndependence` proves
`AdelicSpreadTopologyIndependenceStatement`.
`curvePlaceSpreadTopologyIndependence` and
`numberFieldSpreadTopologyIndependence` prove its two clauses.
The conclusion is equality of the independently constructed topologies on
one actual full-adele point type, for two arbitrary finite-type models and
arbitrary specified isomorphisms of their generic fibers with the same
field-scheme.

The hypotheses are exactly those of the target. The curve branch allows
any perfect constant field with the specified compatible rational-function
scalar tower and function-field structure. The number-field branch uses
the full `Adeles K`, including every infinite factor. Both initial finite
sets may be empty; the models and the common generic-fiber scheme may be
nonaffine and nonseparated. Finite type means locally of finite type and
quasi-compact for each structure morphism.

This is a derived proof of the explicit independence target motivated by
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.6 after Remark 3.5 and (3.5.1), and the opening of section 4
on printed p.9. The implementation uses the actual integer-ring colimit,
prescribed-isomorphism descent for scheme models, initial-set invariance
and same-base model-isomorphism functoriality. The helpers below are
internal categorical and topological arguments; they do not introduce
additional arithmetic assumptions.

The general scheme helper conjugates the scheme-limit cone by the two
pullback symmetries to put all model pullbacks in the standard `Over`
order. Its cone leg has first projection equal to the original model
projection and second projection equal to the limit projection followed
by the corresponding integer-spectrum cone leg. Applied to a prescribed
isomorphism of the limit pullbacks, `exists_level_isomorphism` descends it
to a finite stage. The helper retains the commutative square between the
actual cone legs and the prescribed isomorphism, rather than merely
asserting the existence of some stage isomorphism.

Each arithmetic specialization uses the actual field-valued integer-ring
colimit and `spectrumConeIsLimit`. `adelicSIntegersNoetherian` makes the
original integer base Noetherian. The finite-type models are consequently
locally Noetherian, and the required quasi-separatedness and local finite
presentation follow by Mathlib instances. The cone square therefore
applies to these models without imposing separatedness. The arithmetic
cone-leg point identity is proved by the two pullback projections: the
first uses the generic-fiber and initial-set point-equivalence identities;
the second uses the original field-to-adeles diagonal and the literal
integer inclusions.

For models over the same initial integer ring, descend the composite of
the first prescribed generic-fiber isomorphism with the inverse of the
second. Compose initial-set enlargement for the first model, the
homeomorphism induced by the descended model isomorphism, and inverse
initial-set enlargement for the second model. The retained descent square
and first-projection formulas show that this homeomorphism gives the
prescribed composite on actual generic-fiber points. Postcomposing with
the second specified isomorphism identifies the resulting map on the
common field-scheme points with the first specified identification.

For an inclusion of initial sets, `modelPullbackCompIso` identifies the
generic fiber of the enlarged model with the original generic fiber.
Its composite-first-projection formula proves compatibility with the
initial-set point equivalence: apply the inverse original generic-fiber
point equivalence, use its injectivity, and compare the underlying model
morphisms. Initial-set invariance thus yields equality of the two
transported topologies for this enlargement.

For arbitrary initial sets S and U, enlarge both to S union U. Apply the
enlargement equalities on the two sides and the same-base comparison in
the middle. A common topological helper proves each equality by writing
the transported topology as the topology induced along the inverse point
equivalence, using the intervening homeomorphism's induced-topology
identity, and cancelling the compatible point equivalences. This gives
literal equality on the original actual point type. The number-field
proof implements the same steps with its own integer diagram and diagonal.

This proof establishes spread independence. Existence of arithmetic
spreads for all finite-type field-schemes, agreement with other point
topology constructions, and the remaining conclusions of the paper are
separate results.
