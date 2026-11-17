# Faithful quotient pushouts from equality of full point images

This internal construction works over a complete ultrametric normed field
`K` and a normed extension field `L`. The algebra, space and extension-field
universes are independent. Every presentation is saturated, with its space
and chart-index universes equal. No completeness or ultrametric condition
on `L` is needed.

Let `p` be a full field point on `P`, and let `r : P → A`, `s : P → B`,
`f : A → C` and `g : B → C` be complete strong morphisms. Assume that
the full point obtained by first mapping `p` through `r` and then `f`
equals the full point obtained through `s` and then `g`. These are
equalities of entire field points, including all containing-chart
evaluations and their restriction compatibility. Equality of the
strong composites is not required.

Choose a chart `k` containing `p`, charts `i` and `j` receiving the
complete images of `k` under `r` and `s`, and a common target chart
`t` receiving the complete images of `i` under `f` and `j` under `g`.
The theorem `chartTestPullback_square_of_point_map_eq` identifies the
two bounded maps from the algebra of `t` to the faithful local
quotient of the algebra of `k`.

The proof applies the descended injective character of that quotient.
For each leg, `character_comp_chartTestPullback` evaluates the actual
quotient-valued pullback as the bounded evaluation of the first full
image point. The actual `map_boundedEval` formula then computes its
composition with the next chart pullback as evaluation of the
second full image point. The assumed full-point equality identifies
the resulting evaluations at `t`; proof irrelevance identifies their
membership witnesses. Injectivity of the quotient character gives
the desired exact equality of bounded maps.

The definition `chartTestPushoutPullbackOfPointMapEq` applies the
universal property of the actual affinoid pushout of the pullbacks
from `t` to `i` and `j`. Its target is the actual local kernel quotient,
a complete ultrametric normed commutative `K`-algebra. The resulting
bounded map recovers each original quotient-valued chart pullback
on composition with the corresponding pushout leg. The two leg
identities also determine it uniquely by the pushout's bounded-map
extensionality theorem.

The provenance is internal, from the actual full-point pushforward
formula, evaluation-kernel quotient and affinoid pushout universal
property. This supplies the algebraic compatibility needed when a
square commutes after localization and hence on full point images.
It does not assert smallness of the pushout spectrum, construct a
geometric pullback, use a domain completed-residue comparison, or
prove the final localized full-field-point preservation statement.
