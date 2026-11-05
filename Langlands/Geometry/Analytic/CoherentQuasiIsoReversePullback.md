# Reverse bounded chart pullbacks without directedness

This module constructs bounded reverse maps on pairs of original charts
whenever the target chart is contained in the image of the source chart.
It proves their spectrum equation, full domain representation, naturality
under restrictions in both variables, and forward/reverse factorization.

## Inputs and meaning

The common assumptions are a complete ultrametric normed field `K` and actual
`AffinoidAtlasPresentation` objects `A` and `B`. Their ambient spaces have
universe `v`, and their chart indices have an independent universe `w`; the
field has universe `u`. No nontrivial-valuation instance is required.
Write `f : StrongHom A B` for the given all-admissible-pair strong map and
`hf : f.IsQuasiIso` for its full quasi-isomorphism property. This property
includes the ambient homeomorphism and full `Represents` conditions for all
admissible original chart pullbacks.

For source index `i` and target index `j`, assume

```text
range (B.chart j) ⊆ f.baseMap '' range (A.chart i).
```

The object `A.atlas.originalLocalDomain i` is the whole full domain in the
original chart, with its actual original presented algebra.
`hf.domainImage` sends it to an actual local full domain in `B` with the same
algebra and ambient locus `f.baseMap '' range (A.chart i)`.
These objects, their bounded restrictions, and their full representations
come from the imported constructions.

The final two results additionally require `hc : f.HasCoherentPullbacks`.
This is the existing intrinsic coherence law on the original pullbacks,
expressed on all presented-affinoid coefficient tests. It is an input law
on `f`, rather than the assumption of any reverse map or reverse-map equation.

## Constructed maps and full representation

`reverseChartInclusion j i h` applies the actual local-domain category's
`Inclusion.ofSubset` to the displayed containment. Its source is the whole
original target chart and its target is the direct image of the whole
original source chart. The domain-image and original-chart locus equalities
prove the required containment.

`reverseChartPullback j i h` is this inclusion's stored restriction:

```text
BoundedAlgHom K (A.atlas.algebra i) (B.atlas.algebra j).
```

Thus the construction retains the original chart algebras in the
contravariant algebra direction. A bounded inverse between the complete
original algebras is not required.

`reverseChartPullback_chart` proves, for each spectrum point `x` of the
original target algebra,

```text
f.baseMap (A.chart i (comap reverseChartPullback x)) = B.chart j x.
```

The proof uses the actual inclusion's ambient naturality square. The
domain-image ambient-map equation and the two original whole-chart
ambient-map equations express that square in the original charts.

`reverseChartPullback_represents` proves the full `Represents` condition
for this bounded map at the subset

```text
{x : BanachSpectrum (A.atlas.algebra i) |
  f.baseMap (A.chart i x) ∈ range (B.chart j)}.
```

The inclusion already represents the inverse image of its source locus
under its target ambient map. Function equality for the image ambient map
and the original target-chart locus equality identify that subset with the
displayed one. The proof transports the entire full representation along
this set equality. In particular, it retains unique bounded factorization
for every presented-affinoid coefficient algebra, beyond the pointwise
spectrum equation.

## Naturality as entire bounded maps

`reverseChartPullback_naturality hc` takes original restrictions
`range (B.chart j) ⊆ range (B.chart j')` and
`range (A.chart i) ⊆ range (A.chart i')`, and image containments for `(j,i)`
and `(j',i')`. It proves

```text
B.restriction j j' ∘ reverse(j',i')
  = reverse(j,i) ∘ A.restriction i i'.
```

Composition here is `BoundedAlgHom.comp`. Construct the two original
whole-chart inclusion arrows. The two routes from the original target
chart `j` to the image of the original source chart `i'` are equal in the
actual local-domain category. Its thinness was proved using full bounded-test
uniqueness. The image arrow exists under `hc` and stores exactly the
original source restriction. Applying the restriction projection to this
arrow equality, then recovering original whole-chart restrictions, gives
the asserted equality of entire bounded maps.

`reverseChartPullback_comp_pullback hc` takes any original target chart `q`
containing the entire image of source chart `i`, together with the target
containment `range (B.chart j) ⊆ range (B.chart q)`. It proves

```text
reverse(j,i) ∘ f.pullback i q = B.restriction j q.
```

Apply the reverse inclusion's structural equation over `q`. The image
domain's chart restriction is the constructed `localChartPullback`.
Under `hc`, parent admissibility identifies it with the original forward
pullback after the whole source domain's identity base map. The structural
restriction of the whole target domain into `q` is its original atlas
restriction. These are equalities of complete bounded algebra maps.

## Provenance and scope

This is an internal derivation from `StrongQuasiIsoDomainImage`,
`AtlasSaturationComparison`, the actual local-domain category, and coherent
local pullback recovery. It introduces no new external-literature assertion.
All new reverse maps are constructed by actual full-domain inclusion; their
bounded equalities use full-test uniqueness and structural equations.

No directedness, upper cofinality, or closure under all local domains is a
hypothesis. This module does not assert that enough original target charts
satisfy the image containment to cover the target. Constructing such a
locally refining selection, a reverse strong morphism, arbitrary
quasi-isomorphism refinement squares, and the full analytic and equivariant
sites remain separate obligations. The Harris tower specialization also
remains open.
