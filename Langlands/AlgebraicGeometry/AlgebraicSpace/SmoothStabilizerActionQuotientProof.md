# Quotients by smooth group actions with smooth stabilizers

Worker 4778 and Worker 5132 prove
`Langlands.AlgebraicGeometry.AlgebraicSpace.smoothStabilizerActionQuotient.{u}`. Its type
is exactly the published `SmoothStabilizerActionQuotientStatement.{u}`. The statement's
Lean/Markdown pair and its import closure are unchanged.

## The implemented proof

Let `G` be a group scheme smooth over `S`, acting by `a` on a scheme `V` locally of finite
type over `S`. Assume the stabilizer scheme is smooth over `V`. The proof forms two
quotients, each by the Library's smooth relation quotient theorem
`smoothRelationQuotient`.

1. **First quotient** (`SmoothStabilizerActionArrows`,
   `SmoothStabilizerActionOrbitRelation`, by Worker 4778).
   - The arrow scheme `R = (G × V) ×_{V × V} (G × V)` is the kernel pair of the action
     graph `(g, v) ↦ (g.v, v)`.
   - The map `((g, v), (g', v)) ↦ ((g' g⁻¹, g.v), (g, v))` identifies `R` with the base
     change of the stabilizer projection along the action map
     (`isPullback_arrowToStabilizer`). So both projections of `R` are smooth.
   - `smoothRelationQuotient` applied to `R` gives an algebraic space `B`. It is the
     canonical étale quotient of `G × V` by `R`, with a smooth surjective quotient map
     `q`.
   - The graph descends to a monomorphism `B → V × V`, with endpoints `s'` and `t'`.
     Then `q ≫ s'` is the action map and `q ≫ t'` is the projection.
   - `q` is étale locally surjective.
   - `s'` and `t'` have smooth projections: along the smooth surjective cover `q` they
     become the action map and the projection, which are smooth.

   `exists_orbitRelationSpace` records this data.
2. **Second quotient and comparison** (`SmoothStabilizerActionQuotientAssembly`, by
   Worker 5132). `actionQuotient_of_relationSpace` takes exactly this data and proves the
   statement's conclusion for `a`.
   - `(s', t')` is an equivalence relation on `V`.
   - A second application of `smoothRelationQuotient` makes its canonical étale quotient
     an algebraic space with a smooth surjective quotient map from `V`, and with an atlas
     locally of finite type over `S`.
   - This quotient map is an fppf coequalizer of the action and the projection. Any other
     fppf quotient of the action is isomorphic to it, and smoothness, surjectivity and the
     atlas transport along the isomorphism.

The theorem `smoothStabilizerActionQuotient` introduces the hypotheses of the statement.
It obtains the data of step 1 from `exists_orbitRelationSpace` and concludes with
`actionQuotient_of_relationSpace`. The Markdown files of the three helper modules
describe the details.

## Provenance

The route follows the Stacks Project's proof of Proposition 101.28.9 (Tag 06QJ),
(2) ⇒ (1), as cited by the statement's Markdown. That proof first forms `R' = R/G`, the
quotient of the arrow space of the groupoid by the free action of the stabilizer, with
Bootstrap Lemma 80.11.7 (Tag 06PH). It then forms `U/R'` with Bootstrap Theorem 80.10.1
(Tag 04S6). Here the groupoid is the action groupoid `G × V ⇉ V`, and all flatness
hypotheses are smoothness hypotheses.

The orbits of the stabilizer's free action on `G × V` are the classes of the relation
`(G × V) ×_{V × V} (G × V)`. So the implemented proof forms `R'` as the quotient of
`G × V` by that equivalence relation. Its projections are smooth, so the proof uses the
smooth case of Theorem 80.10.1 (`smoothRelationQuotient`) in place of Lemma 80.11.7. The
second step uses the same theorem, as in the source.
