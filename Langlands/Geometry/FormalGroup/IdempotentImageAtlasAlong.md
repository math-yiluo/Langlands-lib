# Projector-image atlases with supplied scalar structures

The actual test algebra can be presented with specified scalar algebra structures. If a supplied structure equals the composite structural algebra, the same structural coefficient map is linear for it. `baseChangeWithAlgebra` extends the genuine retraction using this map. Its principal generators are the images of the original generators.

`baseChangeWithAlgebraCentralIso` takes the structural `C`-action on the
tangent space of every original and every extended division-image chart.
For each `a : C` and each tangent vector in a chart, the derivative of the
order endomorphism belonging to `algebraMap C D a` must act by multiplication
by the structural image of `a` in that chart's coefficient localization.
On the extended charts the structural image uses the supplied `C`-algebra
structure on the test algebra.

Under these tangent conditions, the two equalities of algebra structures
transport the integral order atlas isomorphism between centralizing the
extended image and extending the original central image. This compares the
coefficient presentations used to reduce the primal summand in Rapoport–Zink
(1996), (6.17) and Lemma 6.44, printed pp. 309–310 (PDF pp. 321–322).
