# Retraction distance on an integer-valued building

This module contains the generic construction from
`UnramifiedRetractionDistanceProof`, with the same public names, hypotheses,
statements and proof source. Worker 5428 authored that construction; Worker 202
separated its imports so it can be used without the downstream unramified metric
statement modules. The original maximal-unramified theorem remains in its original
module, importing this construction.

For arbitrary universe `u`, let `B : IntegerValuationBuildingData v G` over a field
`k` with integer valuation `v`. The datum already supplies connected reductivity,
a maximal split torus, the apartment and full V6 compatibility. The theorem
`IntegerValuationBuildingData.exists_retractionDistance` assumes only an order-one
unit and constructs a real-valued function `d` on the original quotient with:

- invariance under its existing rational-point action;
- restriction to `KPApartmentData.rootDistance` on the supplied apartment;
- for every apartment point `a`, a retraction onto that apartment which fixes it,
  contracts `d`, and preserves distances from `a`.

No metric on the building is assumed or constructed in this module. The apartment
uses the existing root-coordinate norm and metric from
`IntegerValuationBuildingMetricReduction`.

The chosen distance is the root distance in a common translated apartment.
The published two-point normalizer comparison proves chart independence and
invariance. Chamber transitivity and the sharp chamber cover give the mixed
factorization `g = p n q` with sharp chamber fixers on the two sides. This supplies
a chamber retraction. Equal distances from an open chamber prove uniqueness:
evaluating squared norms at a regular point and a small displacement forces the
squared difference norm to vanish. The retraction agrees with one normalizer on
each closed facet in a translated apartment. The existing facet-closure Lipschitz
lemma then gives global nonexpansion. Choosing a chamber whose closure contains
`a` proves preservation of distance from `a`, because its sharp fixer fixes `a`.

This is a meaning-preserving import extraction of the internally derived
construction described in the paired Markdown of
`UnramifiedRetractionDistanceProof`. Its mathematical context is KP Proposition
1.5.24, Definition 1.5.25 and Lemma 4.2.2; no new source assertion is introduced.
The complete proof explanation, notation and declaration table remain in that
companion. The explicit retraction theorem retains its order-one-unit hypothesis;
its maximal-unramified specialization discharges that hypothesis with the existing
uniformizer theorem. This extraction does not assert existence of a supplied
datum or a stable apartment over the base field.
