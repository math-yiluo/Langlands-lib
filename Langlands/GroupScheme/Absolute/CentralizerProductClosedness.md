# Closedness from rational closure points

Internal implementation by Worker 1438, derived from the imported Mathlib
constructibility and Jacobson-space theorems and the accompanying conditional
conjugacy reduction. It supplies no proof of the main Borel-intersection
statement.

The topological helper proves that a nonempty constructible subset of a
Jacobson space contains a closed point. Boolean-subalgebra induction expresses
constructible sets as finite unions of differences of open retrocompact sets.
Each difference is locally closed, where the Jacobson property supplies the
point. In a Noetherian Jacobson space, the constructible difference between a
closure and the original constructible set is therefore empty as soon as every
closed point in the closure belongs to the original set.

For finite-type schemes over an algebraically closed field, Chevalley's theorem
makes a morphism's image constructible. Every closed point of the target is
represented by a rational point, with singleton underlying image. An explicit
hypothesis that every rational point whose image lies in the closure factors
through the morphism therefore puts every closed point of the closure in the
image. The topological helper proves that image is closed.

For the actual multiplication morphism `M × B → G`, local finite type and
affineness of both factors give a finite-type source. The target is assumed
locally of finite type and quasi-compact over the same field. A rational point
of `G` whose image lies in the topological product closure lifts to its actual
reduced closed subscheme, since `Spec k` is reduced. Thus supplied rational
factorization for points of that reduced closure meets the preceding criterion.
The internal proposition `HasRationalClosurePointLifts j b` names exactly this
lifting condition; its definition needs only a field, while the closedness
conclusion uses algebraic closure.

The final theorem applies the accompanying conjugacy reduction when `M` and
`B` are smooth, affine and connected, `M` represents the full dynamic centralizer
of the cocharacter `χ`, and the closed monic subgroup `B` contains its full
range. It assumes a supplied homomorphism `q : B → D` with split torus target
and that every cocharacter in `B` with the same projection as the restricted
cocharacter is conjugate to that restriction. This explicit conjugacy input
remains unproved here. Neither quotient existence nor surjectivity of `q` is
assumed or concluded by this module. The resulting closedness assertion is about
the actual underlying topological image, rather than only its rational points.
