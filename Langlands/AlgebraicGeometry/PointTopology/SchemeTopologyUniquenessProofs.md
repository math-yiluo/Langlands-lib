# Uniqueness from affine characterization and actual open chart coverage

Authors: Worker 105 (proof), Worker 1103 (check and submission). This unit
proves `Langlands.AlgebraicGeometry.PointTopology.SchemePointTopologyUniquenessProperty`
through `schemePointTopologyUniqueness_proof`, with exactly the target's full
parameter order and hypotheses. It uses the actual relative scheme-point
carrier `RingPoint R X S` throughout and the independently defined
affine-chart final topology `schemePointTopology`.

## Topology determined by open affine charts

`schemePointTopology_eq_of_openCharts` is a topology determination lemma for
an arbitrary actual relative scheme `X` over `Spec R`, with no finiteness
assumption on `X`. Suppose that for every affine open `U` of `X` the point
map `openPointMap R X S U` of the actual open inclusion, with the existing
evaluation topology on the affine chart, is an open embedding into a topology
`T`. Then `T = schemePointTopology R X S`. By the defining open-set criterion
`schemePointTopology_isOpen_iff`, a set is open for the final topology exactly
when its inverse image in every affine chart is open. Opens of `T` have open
inverse images by continuity of the open embeddings. Conversely, suppose all
chart inverse images of a set `V` are open. By `exists_affineOpenPoint`, which
uses that `S` is local, every point of `V` comes from some actual affine chart.
The image in `T` of that chart's inverse image of `V` is open, because an open
embedding is an open map; it contains the point and lies in `V`. Hence `V` is
open in `T`. This step uses only localness of `S`, with no open-unit or
ring-operation assumption.

## Restriction of the five axioms

`schemePointTopologyAxioms_toAffines` restricts the arbitrary full scheme
assignment and its five source requirements to finite-type affine schemes.
Functoriality, pullback, closed-immersion and affine-line clauses become
exactly the four clauses of `AffineSchemeTopologyAxioms`; the open-immersion
clause is retained for the final step.

## Main proof

The main proof applies the published four-axiom uniqueness theorem
`affineSchemeTopology_eq_evaluation` to the restricted assignment. This gives
equality with the evaluation topology on every finite-type affine scheme over
`Spec R`. For a locally finite type `X` and an affine open `U`, the actual open
subscheme `openOver R X U` is affine, and its structure map `U.ι ≫ X.hom` is
locally of finite type. So the assignment on this chart is the evaluation
topology. The actual open inclusion `openOverι R X U` has the open-immersion
property, and its point map is precisely `openPointMap R X S U`. The full
assignment's open-immersion axiom therefore gives the hypothesis of the
determination lemma for `T X`. Applying the lemma to every scheme gives
equality of the complete assignments with `evaluationSchemePointTopologyFamily`.

The proof uses the functoriality, pullback, closed-immersion, open-immersion
and affine-line axioms, the `IsTopologicalRing S` hypothesis required by the
affine characterization theorem, and localness of `S`. The target's
`IsOpenUnits S` hypothesis is retained in the signature, but this argument does
not use it; it matters for the separate existence assertion.

## Source

This proves the uniqueness clause derived from Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Proposition 3.1,
printed page 4. There the proof reduces to open immersions between affine
schemes and leaves the rest to gluing; the Lean proof above instead combines
the affine characterization with the open-immersion axiom and the cover of
actual points by affine charts. The extension to an arbitrary base `R` and a
value algebra `S` is explained by the relative-point proof above. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This unit supplies uniqueness only; the existence of an assignment satisfying
the axioms and the other assertions of the paper are separate obligations.
