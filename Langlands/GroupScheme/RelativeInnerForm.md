# Étale inner forms and comparison descent over arbitrary schemes

This internal derived module extracts the existential inner-form predicate
from the semi-local quasi-split inner-form statement. For an action `a` of
`A` on `G`, `a.IsEtaleInnerForm H` means that an étale surjective scheme
`U → S` supports a natural family `LocalGroupIso G H U` with inner
discrepancy after every restriction of every test scheme. This is exactly
the predicate in that target, without its semi-local, reductivity or
quasi-split hypotheses.

`LocalGroupIso.ofIso` assigns to any actual isomorphism its constant family
on any parameter scheme. Its discrepancy is the identity acting point.
The identity cover therefore proves that any isomorphic group is an
étale inner form, including reflexivity.

For symmetry, composition and comparison, the supplied maps `G → A` and
`H → B` are fppf quotients by the full centres, and their specified actions
restrict to conjugation. Symmetry uses the inverse family and the induced
equivariant quotient family. Composition uses the product of the two
parameter schemes, pulls back the two families along its projections, and
applies the local inner-discrepancy composition theorem. This fibre
product remains étale and surjective over `S`. Comparison follows by
inverting the first family and composing with the second. Quotient maps
and actions for the relevant intermediate groups remain explicit inputs;
the module does not assert that such quotient data exist.

`LocalGroupIso.comparisonInnerCocycle` is the natural `B`-valued cocycle
of the product-cover comparison family. It is constructed from its inner
discrepancy and the faithfulness of the full-centre quotient action.
The companion discrepancy theorem verifies its meaning.
`comparisonIsoOfTrivialInnerCocycle` twists the comparison family by a
cobounding cochain and applies the published fppf descent construction,
giving an actual isomorphism `H ≅ K`.

The final theorem applies this descent to the existential inner-form
presentations. It assumes triviality of the constructed natural cocycles
for inner local families between the two specified forms. This is a
conditional reduction: it does not assert vanishing of all cocycles in
an adjoint group. Neither the necessary vanishing result nor existence
or uniqueness of quasi-split inner forms is proved here.

The provenance is internal: the constructions use the published local
isomorphism, full-centre quotient equivariance, faithful discrepancy
cocycle, and fppf descent interfaces. The implementation and all retained
hypotheses are described above; no new original-literature result is
claimed.
