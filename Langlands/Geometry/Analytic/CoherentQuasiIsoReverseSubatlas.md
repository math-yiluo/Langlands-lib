# Actual reverse maps on locally refining original target subatlases

This file is an internal construction from actual affinoid atlas maps, their
local-domain categories, and finite relative neighborhood refinements. It
constructs a reverse strong quasi-isomorphism on a selected target subatlas.
It does not cite a new external result or identify the construction with a
numbered assertion in the literature.

## Objects and hypotheses

Work over a complete ultrametric normed field `K : Type u`. Let `A` and `B`
be actual affinoid atlas presentations with ambient spaces in `Type v` and
chart indices in `Type w`. Their chart algebras are presented affinoid
algebras, and their restrictions are actual bounded algebra homomorphisms.
The three universes are independent.

Let `f : StrongHom A B` and `hf : f.IsQuasiIso`. This means that the ambient
map is a homeomorphism and every admissible supplied chart pullback represents
its chart image in the full sense of `Represents`: a closed locus with the
specified spectrum image and unique bounded factorization on every
presented-affinoid coefficient test.

The selection and its local refinement use
`hb : B.atlas.HasAllLocalDomains`. This says that every actual local domain
of `B` has the same ambient locus as an original `B` chart. Construction
of the reverse strong map also uses `hc : f.HasCoherentPullbacks`, the
intrinsic coefficient-test compatibility of the original forward pullbacks.
There is no directedness, upper cofinality, or source full-domain-closure
hypothesis.

## Two reusable refinement lemmas

`AtlasTopology.IsQuasinet.locallyRefines_intersectionFamily` works on any
topological space. If a family `υ` is a quasinet and `τ` is any family,
then `intersectionFamily τ υ` locally refines `τ`. For a point of a member
`U` of `τ`, intersect each member of a finite ambient neighborhood witness
from `υ` with `U`. The resulting finite union is a neighborhood relative to
`U`, and all its members contain the point and lie in `U`. This is a
topological construction of subsets; it asserts no affinoid representation
of these intersections or their union.

`IndexedAffinoidAtlas.subatlas_hasAllLocalDomains` says that a downward
closed, locally refining selection of original charts preserves
`HasAllLocalDomains`. Given a local domain of the selected atlas, view it
as the same local domain with the same algebra in the original atlas.
Original full-domain closure realizes its locus by an original chart.
The locus lies inside its selected parent chart, so downward closure
selects that realizing chart. The converse containment of chart families
in local-domain families is the existing whole-chart construction.
This proves equality of the two families of ambient loci; it makes no
identification of their chosen algebras.

## The selected original target charts

`hf.reverseChartSelection j` is the proposition

```text
there exists i such that
range(B.chart j) ⊆ f.baseMap '' range(A.chart i).
```

The quasi-isomorphism argument is explicit in this definition. Its body
uses the forward map and the original chart loci; it assumes no reverse
map or output atlas. `reverseChartSelection_downward` follows by
transitivity of containment.

`reverseChartSelection_locallyRefining hb` proves finite relative local
refinement inside every original target chart. Transport the original
source chart quasinet through the ambient homeomorphism. The first
topological lemma refines each target chart by its intersections with
transported source charts. Each transported whole source chart is the
locus of its constructed local-domain direct image. Target full-domain
closure, through `imageOriginalChartIndex`, realizes this entire locus by
an original target chart. The original target net supplies a finite
relative refinement of each intersection by original target charts
contained in that intersection. Every such chart satisfies the selection.
Transitivity of relative local refinement gives the result.

`reverseSubpresentation hb` is the existing same-space subpresentation for
this proved locally refining selection. Its indices are the selected
original target indices, and it keeps their original algebras, embeddings
and bounded restrictions. The selected family is a net by the existing
subatlas construction. `reverseSubpresentation_hasAllLocalDomains hb`
applies the downward-selection lemma, so this new atlas also has
full-domain closure.

## The complete reverse map

`reverseStrongMap hc hb` is an actual strong map

```text
reverseSubpresentation hf hb ⟶ A.
```

Its ambient map is `hf.inverseBaseMap`, the continuous inverse of the
original ambient homeomorphism. Each selected target chart has an
original source chart containing its inverse image, by the defining
selection and `inverse_admissible_iff`.

For every selected original target index `j`, every original source
index `i`, and every admissibility proof, the stored pullback is
`hf.reverseChartPullback j.val i ...`, from `A_i` to `B_j`. This bounded
map was constructed in `CoherentQuasiIsoReversePullback` from an actual
inclusion of local domains. The ambient square follows from its spectrum
equation and the two ambient inverse identities. Two-variable
compatibility with all original restrictions is exactly its previously
proved bounded naturality under `hc`. Thus the construction stores every
admissible bounded pullback, rather than choosing only one target chart
per source chart. `reverseStrongMap_baseMap` and
`reverseStrongMap_pullback` record these defining equalities.

`reverseStrongMap_isQuasiIso hc hb` proves the full quasi-isomorphism
property. Its ambient map is the inverse homeomorphism. For each
admissible pair the existing reverse-chart representation has locus

```text
{x in spectrum(A_i) | f(A.chart i x) lies in range(B.chart j.val)}.
```

The inverse ambient identities identify this with

```text
{x in spectrum(A_i) |
  A.chart i x lies in inverseBaseMap '' range(B.chart j.val)}.
```

This is exactly the chart-image locus of the reverse strong map.
Transport along this equality preserves the whole `Represents` predicate,
including its universal bounded factorization, on the original algebras.
The proof does not infer equality of bounded algebra maps from equality
of spectrum maps.

## Local compatibility and remaining scope

`reverseStrongMap_hasCoherentPullbacks hc hb` applies the existing result
that strong maps from a full-domain-closed atlas have intrinsic coherent
pullbacks. The required source closure was proved above.
`reverseCompatibleStrongMap hc hb` uses `CompatibleStrongHom.ofSaturated`
to package the same continuous map and all bounded pullbacks with their
actual local inverse-image compatibility. Its `toStrongHom` is
definitionally the constructed reverse strong map, as recorded by
`reverseCompatibleStrongMap_toStrongHom`.

This unit proves the selection, its local refinement and closure, and a
full compatible reverse strong quasi-isomorphism. It does not yet prove
the two whole-arrow composite equations with the original forward map
and the subatlas inclusion, a general Ore refinement square, the
analytic morphism category comparison, etale or quasi-etale sites,
equivariant sites, or the Harris tower specialization. Those remain
obligations of the surrounding analytic-space and site construction.
