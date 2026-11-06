# Full Tate-normalized models and the original Harris CM classes

Author: Worker 344.

This internal comparison works over an existing admissible connected CM test
base, at a fixed original Harris level and a geometric point. It uses the
actual `TateNormalizedCMRepresentative` from the normalization construction:
one polarized abelian scheme with the original normalized CM determinant
and geometric dimension, an actual action of the Harris integral order,
and the original full integral Tate level condition.

`TateNormalizedCMRelated` restricts the existing `IntegralCMRelated` to
these representatives. Thus it retains the original rational-isogeny
relation, expressed by exact integral polarized witnesses and the
original transported level equation. It does not require the underlying
schemes to be isomorphic. The published class-equality criterion proves
that this relation is exactly equality of the forgotten original CM
classes. This proves its equivalence laws and defines
`TateNormalizedCMIsoClass`.

The representative-class map descends to `tateNormalizedCMForget`.
Its injectivity is unconditional: quotient induction reduces equality
to the same original class-equality criterion. The map
`tateNormalizedCMToIntegralClass` forgets only the full Tate normalization
into the existing integral-action quotient. Both routes to the original
CM classes agree literally on representatives and hence on the quotient.
This also proves injectivity of the latter map. No existence theorem is
used for any of these facts.

The existence section explicitly assumes
`ProperFibreAmpleAffineOpenStatement` and
`CommensurableInvariantLatticeRealizationStatement`. The geometric point
also has characteristic zero, and the original level's image preserves
the fixed Harris integral source span. For any original CM class, the
published representative-surjectivity theorem supplies an actual
representative satisfying the original determinant and dimension tests.
Its actual polarization supplies the finite-set source fibre-affineness
premise through `DualWitness.forall_finset_fibre_affine`, using the fixed
diagonal polarization bundle and the stated proper-family theorem.
The existing normalization assembly then realizes its original carried
lattice on an actual abelian scheme, retaining the exact rational
comparison, the actual polarization, the original CM condition and
an actual integral order action on that same scheme. The assembly's
class theorem identifies its original CM class with the chosen class.

Consequently `tateNormalizedCMRepresentative_exists` and
`tateNormalizedCMForget_surjective` cover the entire original CM class
set under these explicit premises.
`tateNormalizedCMClassEquiv` is the resulting equivalence whose forward
map is exactly forgetting. Injectivity ensures that all choices of
realized models and normalized frames give the same inverse class.
Surjectivity of the map to integral-action classes follows by applying
this result to their original CM class and using injectivity of the
published integral forgetful map.

All content is internally derived from the named published constructions.
The two generic geometric statements remain assumptions here. This
fixed-base, fixed-point and fixed-level comparison constructs no
representing scheme, establishes no output admissibility, and asserts no
naturality in geometric points, test bases or level arrows. In particular,
it does not prove division-case representability.
