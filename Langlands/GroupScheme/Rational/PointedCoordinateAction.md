# Actual pointed affine schemes and equivariant coordinate pullback

This derived construction extends the actual-coordinate convention of
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), §3.3,
printed pp.107–108 (PDF pp.133–134), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`, to pointed affine schemes that
need not be groups. CGP uses such schemes for closures of commutator
images. All definitions retain arbitrary universe `u`, every commutative
coefficient algebra, and every field characteristic.

`PointedAction` includes an actual scheme morphism `S × V → V`, its action
laws on every test scheme over the field, and a fixed rational point.
The induced point action is natural under every test morphism.
`PointedAction.ofGroup` forgets the group structure on the target of an
existing `AutomorphicAction`. `IsStableInclusion` requires every translated
point of `V` to factor through its actual inclusion into the ambient group.
Given a monomorphic inclusion and a point mapping to the identity,
`ofStableInclusion` constructs the restricted scheme action: stability at
the universal pair provides its morphism, and cancellation against the
inclusion proves the action and fixed-point laws. The theorem
`ofStableInclusion_act_comp` proves agreement with the ambient action;
`stableInclusion_isPointedEquivariant` includes the fixed-point agreement.
No group structure on `V` is used.

`coordinatePresentation` and `coordinateIso` give an actual affine
presentation of `V` over the field. `pointCoordinates` identifies its actual
algebra-valued points with homomorphisms from this coordinate algebra.
The universal point constructs `pullback`; point naturality proves its
evaluation formula, identity law, and contravariant composition law.
These are coordinates of the given scheme, not a separate representation.

`actionCoordinates` translates the universal point after coefficient
extension to `A ⊗ O(V)`, and `actionPullback` extends the resulting map
`A`-linearly. `evaluate_actionCoordinates` and `evaluate_actionPullback`
prove the exact CGP convention `f(s.v)`, with no inverse on `s`, after
every coefficient change. The extended acting point is fixed and the
universal target point translates by the actual action. These identities
prove the unit and reversed composition laws for pullback. Pullback by
the inverse acting point then constructs `actionAut` as an `A`-algebra
automorphism. These laws use the specified action morphism and its laws.

`augmentationIdeal` is the kernel of evaluation at the distinguished
point, and `augmentation` is the same kernel as a vector subspace.
`action_preserves_origin` proves that every actual action pullback preserves
the base-changed evaluation at that point. The coordinate and augmentation
weight spaces use the equation `f(s.v) = χ(s) f(v)` for every coefficient
algebra and every pair of points. The support consists of weights of
nonzero augmentation eigenfunctions. The zero character is present only
when it occurs. The `ofGroup_weightSpace`, `ofGroup_augmentationIdeal`,
`ofGroup_augmentation`, and `ofGroup_support` equalities identify these
objects definitionally with `CoordinateWeights` for the original group
action; no change of character labels occurs.

`IsPointedEquivariant` requires equivariance on every test scheme and
preservation of the distinguished point. Applying coordinate evaluation
to these equations proves weight preservation and the augmentation
pullback. Injectivity of coordinate pullback preserves the nonzero
augmentation witness, giving containment of target support in source
support. Conversely, `HasWeightwiseLifts` gives containment of source
support in target support. Lifting is an explicit proposition, not an
assumed law of closed immersions. For actual pointed equivariant scheme
isomorphisms, cancellation proves inverse equivariance and point
preservation; pullback composition gives an algebra equivalence, weight
reflection, and equality of augmentation supports.

The separate files `DominantPullbackStatement` and
`ClosedImmersionPullbackStatement` record the remaining geometric
injectivity and quotient targets. The present construction does not prove
those statements, split-torus eigenspace decomposition, or any comparison
with the Lie-kernel support. In particular, it does not assert a
positive-semigroup equality or insert zero into a support.
