# Approximation of actions on supplied cartesian systems

Author: Worker 706.

This internal derived helper joins finite-presentation factorization of an
actual action map with eventual descent of its laws. It uses a supplied
cofiltered diagram of cartesian morphisms of étale equivalence relations,
a cone in that category, and a supplied limit of its object schemes.
Existence of a Noetherian approximation system remains a separate obligation.
All schemes and indexing categories retain the arbitrary universe `u`.

The application is the action-descent step of the proof of Stacks
Proposition 70.8.1, Tag 07SU, in the registered source
`stacks-noetherian-approximation-2026-11-01`. That proposition motivates
the helper; the declarations here are derived from the existing Library
pullback, finite-presentation factorization and action-law descent interfaces.
They neither assume nor prove the full proposition.

Write `D` for the diagram, `F` for its fixed comparison target, `t` for
that comparison, `c` for the relation cone, and `m : c.pt ⟶ F` for the
common composite of its legs with `t`. The supplied object square is
`IsPullback k p q m.objMap`, with `p : P ⟶ c.pt.U`, `q : Q ⟶ F.U`
and `k : P ⟶ Q`. All five declarations lie in
`EtaleEquivalenceRelation.Action.CartesianSystem`.

- `actionCone` is the target-base-change cone whose actual point is the
  action-input scheme `pullback c.pt.s p`. Its level objects are
  `D_i.U ×[F.U] (F.R ×[F.U] Q)`, using the target of the latter arrow
  domain as structural map. It specializes `Action.arrowCone`.
- `actionCone_π_eq` identifies each actual cone leg with the upper-to-level
  `arrowMap`, followed by the target-base-change isomorphism of that level's
  action domain. The proof compares both pullback projections; the second
  projection is checked on its arrow and point projections. The relation
  cone equation and the actual object-cone projection equation identify them.
- `targetFactorMap_compatible` takes a factor `b` to `Q` satisfying its
  structural equation and the factorization of `A.map ≫ k`. Its lifted
  `targetFactorMap` commutes with the actual upper-to-level object leg.
  Both projections of the level object square prove the equality: the
  fixed-object projection uses `actionCone_π_eq` and the factor equation;
  the object-scheme projection uses the over equations of the two maps.
- `exists_compatible_map_at_level` assumes cofilteredness, affine `F.U`,
  `F.R`, `Q` and every `D_i.U`, and locally finite presentation of `q`.
  From the supplied object limit and action `A`, it produces a level and a
  prospective action map on that level's pulled-back object. The map has
  its target equation and commutes with the actual object cone leg.
  Finite-presentation factorization supplies `b`; `targetFactorMap` and
  the preceding compatibility lemma give the result. This declaration
  does not yet assert the unit and associativity laws.
- `exists_equivariant_action_at_level` adds affineness of every `D_i.R`.
  It produces an index `i`, an object `Pi`, maps `pi : Pi ⟶ D_i.U`,
  `li : P ⟶ Pi` and `ki : Pi ⟶ Q`, and a genuine action `B` on `pi`.
  Both squares `IsPullback li p pi (c.π.app i).objMap` and
  `IsPullback ki pi q (t.app i).objMap` hold, `li ≫ ki = k`, and `li`
  is equivariant for `A` and `B` under the actual cone morphism.

For the last result, the proof first obtains a compatible prospective map
at a level `j`. It restricts the relation diagram to `Over j`, using the
preserved supplied object limit. The pulled-back object over `j` is affine
and locally finitely presented, and its composable-input scheme is affine.
`exists_equivariant_action_of_compatible_map` then descends the two action
laws at a common later index, retaining the actual cone leg. Pasting the
two object pullback squares and using naturality of `t` yields the final
square over `Q`; the two cone projection equations yield `li ≫ ki = k`.
The statement retains both squares so properties stable under base change,
such as étaleness, can be transported by a consumer. It does not construct
the object `Q` from an arbitrary finite-presentation object on the limit.
