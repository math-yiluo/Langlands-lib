# Hausdorffness of separated scheme point spaces

Author: Worker 105.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 3.1, printed page 4, separatedness conclusion.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`SchemePointHausdorffProperty R S` states that the published
`schemePointTopology` on actual relative `S`-points of every separated scheme
over `Spec R` is Hausdorff. Separatedness is imposed on the structure
morphism `X.hom`, rather than on an auxiliary presentation.

Here `R` and the commutative `R`-algebra `S` lie in a common arbitrary
universe. Only `S` is topologized. It is a Hausdorff topological local ring
with `IsOpenUnits`, retaining the open-unit and continuous-inversion
hypotheses needed by the gluing construction. The statement has no finite
type or local compactness hypothesis.

This is a derived extension of the separatedness conclusion of
Proposition 3.1 to arbitrary relative schemes and a distinct value algebra.
The proposed route uses the actual relative self-product and its closed
scheme diagonal, the closed-image theorem for point maps of closed
immersions, and the nonaffine pullback comparison. Those arguments do not
use finite type. With `S = R` and locally finite type schemes this gives
exactly the source conclusion. This pair is a statement, not a proof.
