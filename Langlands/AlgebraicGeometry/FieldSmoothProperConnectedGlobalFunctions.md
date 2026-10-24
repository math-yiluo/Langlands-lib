# Global functions of smooth proper geometrically connected schemes over a field

Authors: Worker 361 and Worker 299. Worker 299 specified the field-case
formulation and identified its sources; Worker 361 checked those sources and
the Mathlib interface and implemented this pair.

`Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctions.{u}`
is a proposition definition. In arbitrary universe `u`, it quantifies over
every type `K : Type u` with a `Field K` instance, every scheme
`X : AlgebraicGeometry.Scheme.{u}`, and every morphism
`p : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)`. It asserts

```text
AlgebraicGeometry.Smooth p →
AlgebraicGeometry.IsProper p →
AlgebraicGeometry.GeometricallyConnected p →
CategoryTheory.IsIso p.appTop.
```

The field, field instance, scheme and morphism are quantified inside the
proposition; the three geometric hypotheses are explicit implications.
There are no additional assumptions on the field or the scheme: in
particular no perfectness, algebraic closedness, characteristic, dimension,
projectivity, rational point, reducedness, irreducibility or noetherian
hypothesis is imposed.

The conclusion concerns the canonical map

```text
p.appTop : Γ(Spec (CommRingCat.of K), ⊤) ⟶ Γ(X, ⊤)
```

in `CommRingCat`. Mathlib's `AlgebraicGeometry.Scheme.Hom.appTop` is the
structure morphism's pullback map on sections over the top open.
`CategoryTheory.IsIso` asserts invertibility of this particular map.
Under `AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)`, its source
is canonically identified with `K`; composing the inverse of that
identification with `p.appTop` gives the structure map from `K` to the
ring of global functions on `X`.

The statement uses Mathlib's actual `Smooth`, `IsProper` and
`GeometricallyConnected` predicates. The last requires connected pullbacks
along maps from spectra of fields, so it expresses geometric connectedness
over `K`, including after extending `K`. Its `ConnectedSpace` condition
includes nonemptiness. Thus the empty scheme is excluded without adding a
separate nonemptiness hypothesis.

## Source derivation

This is a derived specialization of Stacks Project Varieties Lemma 33.9.3,
Tag [0BUG](https://stacks.math.columbia.edu/tag/0BUG), item (7). For a proper
scheme over a field `k`, that item identifies its global-section algebra
`A = H⁰(X, O_X)` with `k` when `X` is geometrically reduced and
geometrically connected. Stacks Project Varieties Lemma 33.25.4,
Tag [056T](https://stacks.math.columbia.edu/tag/056T), states that a scheme
smooth over a field is geometrically regular, geometrically normal and
geometrically reduced. Its final conclusion supplies the geometric
reducedness needed in item (7).

Consequently the three hypotheses in Lean supply precisely properness,
geometric reducedness via smoothness, and geometric connectedness for
0BUG(7). The source's identification of the `k`-algebra `A` with `k`
means that the structure map `k → A` is an isomorphism. Transport through
the canonical identification of the global functions on `Spec k` with
`k` gives `IsIso p.appTop`. This explains the source correspondence;
this module states the proposition and does not prove it. Its exact-target
proof remains a separate obligation.

## Retained original sources

Both sources are in the registered collection
`stacks-global-functions-field-and-fibre-criterion-2026-10-23`, HTML snapshot
retrieved 2026-10-23, directory SHA256
`c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`:

- `0BUG.html`, Varieties Lemma 33.9.3(7), and its proof paragraph for (7).
- `056T.html`, Varieties Lemma 33.25.4, statement and proof.

No source-specific project errata note was found when preparing this pair.
The retained 0BUG comments explicitly correct the formerly ambiguous
wording in (7) to require geometric connectedness; the retained statement
already includes that correction. The other comment thread concerns (5)
and does not change (7). The retained 056T page has no comments.
