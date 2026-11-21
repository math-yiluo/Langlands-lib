# Unit orbital integrals in cyclic product coordinates

`cyclicProductUnitOrbitalReduction` proves
`CyclicProductUnitOrbitalReductionStatement`. It compares the twisted orbital
integral of a product subgroup indicator with one twisted orbital integral on
a single factor.

The source group `H` has topological group coordinates
`κ : H ≃ₜ* (Fin (m + 1) → G)`, where `G` is second countable, locally compact,
and Hausdorff. In these coordinates the continuous homomorphism `σ` shifts
each nonfinal coordinate to its successor and applies the continuous
homomorphism `τ` to the first coordinate at the wraparound. Write `y` for
the ordered product of the coordinates of `δ : H`. The ambient measure on
`H` maps under `κ` to the product of copies of the Haar measure on `G`.
The right Haar measures on the twisted centralizers of `δ` and `y` correspond
under the zeroth-coordinate group isomorphism. The quotient measures are
compatible with these ambient and centralizer measures. For a measurable
subgroup `K` of `G` of Haar measure one, the two test functions are the
indicators of the product of copies of `K` in `H` and of `K` in `G`.

The product of the coordinates of the `σ`-twisted conjugate of `δ` by `x`
is the `τ`-twisted conjugate of `y` by `κ x 0`. Consecutive coordinate
factors cancel in this ordered product. The ambient chart uses
`splitCycleChart` to retain the first coordinate of `x` and the nonfinal
coordinates of its twisted conjugate of `δ`. The product identity then
determines the final coordinate. Restricting to the twisted centralizers
gives `cyclicProductCentralizerEquiv`, which reads the first coordinate on
the source and uses the nonfinal coordinates of `δ` to construct its inverse.
Left multiplication by the source centralizer acts through this isomorphism
on the first coordinate of the chart. This gives a homeomorphism of the
source quotient with the factor quotient times the remaining copies of `G`.

The ambient chart transports the Haar measures using
`splitCycleChart_measurePreserving`. For the quotient measures the proof
compares integrals of compactly supported continuous real functions using
the positive quotient lifting theorem, the two compatible-measure integral
formulas, and Fubini. In the resulting quotient chart, membership in the
product subgroup is equivalent to membership of the free coordinates in
`K` and membership of the factor twisted conjugate in `K`. The product
indicator therefore splits into a product of the two indicators. The free
coordinates contribute the product of the masses of `K`, which is one.

This internal reduction implements the change of variables in
Henniart–Lemaire, *Changement de base et induction automorphe pour* `GL_n`
*en caractéristique non nulle*, I.2.4, printed pp. 15–16 (PDF pp. 23–24),
in the unit-function case of I.3.2, printed pp. 25–26 (PDF pp. 33–34). A
field-level application still needs the cyclic algebra coordinates and
the comparison of the norm associations and centralizer measures.
