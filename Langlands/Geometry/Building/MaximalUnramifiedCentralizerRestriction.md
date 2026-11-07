# Actual local centralizer compatibility from unramified restriction

This internal construction specializes actual integer-centralizer field
restriction to the constructed valuation on the actual inertia fixed field
of a nonarchimedean local field. It retains arbitrary universe and the
Library's equal- and mixed-characteristic local fields. No local-field
instance is imposed on the inertia fixed field.

`centralizerValuation_base` identifies the original positive
`Cartan.centralizerValuation` at every original rational centralizer point
with the upstairs integer-normalized centralizer valuation through actual
split cocharacter base change. `centralizerTranslation_base` gives the same
identity for the existing negative local translation. Both use the exact
base-order formula for the constructed inertia valuation and the proved
identification of the original integer-normalized and local centralizer
valuations. The original torus is split; restriction-evaluation bijectivity
is supplied both originally and upstairs. Neither theorem assumes all
upstairs rational centralizer characters descend.

`isCentralizerCompatible_restrict` proves the existing local-field V6
predicate for the literal restricted root-function family. The original
group is affine and locally of finite type. Every original relative root,
centralizer point and root-group point occurs in the conclusion. Supplied
upstairs integer-normalized V6 descends by the general field-restriction
theorem, and the exact normalized local comparison identifies the resulting
predicate with `Building.IsCentralizerCompatible`.

`restrictApartment_isOmegaCompatible` uses the previously constructed
`MaximalUnramified.restrictApartment`, with its exact `localFieldOrder F`,
full valuation orbit and original normalizer action. Here the original
group is smooth and affine, its split-torus inclusion is monomorphic,
and original opposite factor pairs are supplied. The original
`CentralizerDatum` stays unchanged. Upstairs restriction-evaluation
bijectivity for the literal base change of its factorization and V6 for
every family of the supplied upstairs apartment remain explicit inputs.
Every family of the downstairs carrier has an upstairs witness in the
literal restriction image, so family-level V6 yields full existing local
`KPApartmentData.IsOmegaCompatible` on that original actual centralizer.

`restrictOmegaApartment` bundles this apartment and its compatibility in a
subtype. Its value is exactly the existing `restrictApartment`, as recorded
by `restrictOmegaApartment_val`; in particular its carrier is the literal
restriction image of the supplied upstairs class.

The provenance is the general actual centralizer field comparison and V6
restriction, the exact constructed inertia valuation order, the existing
normalized local comparisons, and literal apartment field restriction.
These are internal derived constructions with no new external assertion.
Initial upstairs apartments, upstairs V6 and restriction-evaluation
bijectivity are not constructed. No assertion that the base-changed
original torus is maximal split is made. Larger-torus restriction, quotient
geometry, metric and action continuity, and the supplied-model special
point and unique fixation remain outside this unit. In particular it does
not prove the host's unconditional `BuildingComparisonStatement`.
