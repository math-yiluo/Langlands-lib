# Cartesian lifting of étale splitting charts

`exists_splitChartLift` starts with a multiplicative-type group over
`Spec (A/J)` and a point of that base. It gives an étale chart over `Spec A`
whose pullback to `Spec (A/J)` contains the point in its image and splits the
group. The chart calculation works for any ideal `J`. Nilpotence is used
when passing to a cover of the original base.

Pointwise étale splitting supplies a neighbourhood and a point lying over the
given point. The refinement `exists_standardEtale_chart` takes an affine
open around that point. The affine étale morphism
corresponds to an étale algebra, and Mathlib's standard étale localization
theorem gives a principal open containing the point. Diagonalizability
persists on the refinement by base change.

`StandardEtaleLift.exists_etale_quotient_lift` supplies an étale `A`-algebra
`B` and a compatible surjection `B → C` onto the refined chart algebra.
`quotientChartRingEquiv` uses the first isomorphism theorem to identify `C`
with `B` modulo the ideal extended from `J`. Transporting the published
quotient-ring pushout through this equivalence and applying `Spec` gives
the actual pullback square for the two chart maps.
