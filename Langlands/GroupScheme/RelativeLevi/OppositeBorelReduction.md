# Reduction of the opposite Borel theorem

`relativeOppositeBorel_of_localPresentation_and_lieContainment` proves the
unchanged `RelativeOppositeBorelStatement` conditional on exactly two explicit
proposition premises: `RelativeBorelDynamicPresentationStatement` and
`RelativeParabolicLieContainmentStatement`. Both are proved in other modules,
as `relativeBorelDynamicPresentation` in `BorelDynamicPresentationProof` and
`relativeParabolicLieContainment` in `ParabolicLieContainmentProof`. This
supporting reduction is not by itself an unconditional proof of
`RelativeOppositeBorelStatement`.

The proof obtains closed local opposite Borels and their exact intersections
from the assumed local dynamic presentation and the dynamic intersection
formula. Relative uniqueness, conditional on Lie spreading, makes their ranges
equal on every pairwise overlap. The categorical overlap bridge supplies the
all-test matching condition. Effective étale descent constructs a closed global
subgroup, and the transported local Borel predicates give its relative Borel
property. The local intersection equalities descend to the original base.
Finally, the same relative uniqueness argument identifies every other opposite
Borel with this global one.

The base scheme, reductive group scheme, maximal torus, original Borel and
containment hypotheses are precisely those of the target, in every universe.
The reduction adds no affineness assumption on the base and no restriction on
test schemes. It implements the local construction, uniqueness and descent
route of Conrad, *Reductive group schemes* (2014), Proposition 5.2.12, p.158.
