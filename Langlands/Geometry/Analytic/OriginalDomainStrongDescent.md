# Full strong-map descent along domains containing every original chart

Author: Worker 36.

This derived construction fixes actual indexed affinoid atlas presentations
`A` and `B` over a complete ultrametric normed field, and a family `D` of
original-chart domains of `A`. It constructs a global full strong map from
full strong maps on the actual domains that agree on pairwise intersections,
under the explicit hypothesis that each original source chart is wholly
contained in some member of `D`. The construction retains every bounded
algebra pullback and requires no directedness of the target.

The source conventions are Berkovich, *Etale cohomology for non-Archimedean
analytic spaces* (1993), section 1.1, printed pp.13–14 / PDF pp.10–11
(induced topology, quasinet and net), Definition 1.2.3 and Remark 1.2.4(i),
printed p.16 / PDF p.13 (actual atlases and bounded restrictions),
Definition 1.2.7, printed p.18 / PDF p.15 (full strong maps), and
Definition 1.3.1, printed p.23 / PDF p.20 (contained-chart domain atlases).
The registered source is `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These pages were reread for this unit. The descent construction is derived
from those conventions and the published source-chart reconstruction,
rather than attributed to a separately numbered source assertion.

`OriginalDomainCoversCharts D` says that for every original index `i`,
the actual range domain `ofChart i` is contained in `D k` for some `k`.
`OriginalDomainStrongMatchingFamily A B D` supplies a full strong map from
the constructed presentation of each `D k` into `B`. Its overlap field
requires equality of the entire maps after direct restriction to
`D k ⊓ D l`. Extensionality compares the local-map family, as the remaining
field is a proposition.

`restrict_eq` restricts that overlap equality to any smaller common domain,
using the published transitivity law for full direct restrictions.
`toStrongChartMapData` accepts any selection of a containing member for each
original source chart. Its local map is the selected member's map directly
restricted to the actual source chart domain. For a chart containment,
both members contain the smaller chart, so `restrict_eq` proves equality
of the continuous values. The same equality and the published
`StrongHom.pullback_congr` prove equality of the complete bounded maps at
every admissible target chart. The published direct-restriction
admissibility equivalence first transports the witness from the larger
chart presentation to its family member and then back to the smaller chart
presentation; the original source index and bounded algebra remain the same.

`glueWith` applies the published `StrongChartMapData.toStrongHom`.
Its continuous map is therefore constructed by the actual chart-range
colimit, and its bounded maps and two-variable naturality are constructed
by that published reconstruction. `glueWith_apply_chart` identifies its
value on a chart with the value from any containing family member;
`restrict_eq` makes this independent of the selected member.
`glueWith_apply` then recovers the values on every point of a member,
using the proved coverage of its constructed atlas.
`glueWith_pullback` identifies the entire global bounded map at any original
chart inside a member with that member's pullback, with separate
admissibility witnesses. It uses full equality of the restrictions to that
chart. The member's witness is transported to that chart presentation by
the same direct-restriction admissibility equivalence. The proof does not
infer equality of bounded maps from their spectrum-point values.

`glueWith_restrictSubspace` combines these point and bounded-map formulas
with full strong-map extensionality to recover each supplied local map.
`glueWith_unique` restricts any other proposed global map to a containing
member and then to each original source chart; the published full
source-chart extensionality proves equality. `glueWith_eq` consequently
proves independence of all containing-member selections as an equality
of complete strong maps.

`glue` uses classical choice on `OriginalDomainCoversCharts D` and invokes
`glueWith`. Its restriction and uniqueness laws follow from the preceding
results. Conversely, `StrongHom.toOriginalDomainStrongMatchingFamily`
restricts an actual ambient strong map to all members; full restriction
transitivity proves its overlap equations. The two recovery laws compare
the whole matching-family record and the whole ambient strong map.
`OriginalDomainStrongMatchingFamily.strongHomEquiv` bundles these operations
and both inverse laws.

The coefficient, point and chart-index universes `u`, `v` and `w` are
independent, and the family index has its own universe `z`. No reducedness
or explicit nonemptiness assumption is imposed; the chart-containment
hypothesis retains its literal meaning even for empty domains or families.
For an arbitrary quasinet cover a whole original source chart may straddle
members, so this construction does not establish the full sheaf condition
for `originalDomainStrongPresheaf`. Finite affinoid algebra descent, atlas
saturation and extension, unrestricted strong composition, structure
sheaves, etale and equivariant sites and the Harris tower remain separate
obligations.
