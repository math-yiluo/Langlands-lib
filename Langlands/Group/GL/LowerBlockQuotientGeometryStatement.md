# Geometry of the actual lower-block quotient chart

`Langlands.RankinSelberg.LowerBlockQuotientGeometryStatement.{uF}` is a
Prop-valued definition asserting that the published lower-block chart is an
open embedding, is measurable, and has conull range for every compatible
measure on the large left-unipotent quotient. This module states this
proposition and supplies no proof of its geometry conclusions.

## Internal provenance

The target is extracted from the first three conclusion conjuncts of the
published
[`LowerBlockQuotientDisintegrationStatement` Lean module](../../Representation/RankinSelberg/LowerBlockQuotientDisintegrationStatement.lean)
and its
[paired explanation](../../Representation/RankinSelberg/LowerBlockQuotientDisintegrationStatement.md).
It preserves their canonical structures and actual chart. The auxiliary
small-quotient measure, its compatibility certificate, its unipotent right
invariance instance, and the additive Haar input are omitted because these
geometry conclusions do not involve them. This is an internal statement
extraction; no implication between the two propositions is proved here.
No original literature claim is used as an additional source for this module.

## Fields, ranks and structures

The proposition quantifies over every `p : ℕ` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p` in the independent universe `uF`, and every `n k : ℕ`.
Set `a = n + 1` and `d = k + 1`; both block ranks are positive, including
the cases `n = 0` or `k = 0`. The large rank is `n + 1 + k + 1`.

The local instances are exactly those installed in the disintegration target:
`F.canonicalTopologicalData.topology`, `.valuativeRel`, and `.localField`,
followed by Borel measurable structures and `BorelSpace` instances on

- `F.Carrier`;
- `GeneralLinear (n + 1) F.Carrier` and
  `GeneralLinear (n + 1 + k + 1) F.Carrier`;
- their upper-unipotent groups and their actual `LeftQuotient` spaces;
- `lowerTriangularSubgroup (k + 1) F.Carrier`.

The rectangular matrix space keeps Mathlib's iterated product measurable
structure on `Fin (k + 1) → Fin (n + 1) → F.Carrier`. The domain is the
published right-associated product

```text
LowerBlockQuotientParameters (n+1) (k+1) F.Carrier
  = Q_a × (Matrix (Fin d) (Fin a) F.Carrier × lowerTriangularSubgroup d F.Carrier),
Q_m = LeftQuotient (upperUnipotent m F.Carrier).
```

It has the product topology and product measurable structure from these
factors. No new measurable structure is installed on the matrix or product.

## The actual chart and left-coset convention

The local `chart` is bound directly to the published `lowerBlockQuotientChart`
of [`LowerBlockQuotientCoordinates`](LowerBlockQuotientCoordinates.lean),
with codomain `LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier)`.
The two rank expressions `n + 1 + (k + 1)` and `n + 1 + k + 1` are
definitionally equal. On representatives it sends

```text
([g], x, h) ↦ [lowerBlockPair g x h] = [[[g, 0], [x, h]]].
```

Here `x` has `d` rows and `a` columns, and `h` is an invertible lower
triangular matrix. `LeftQuotient H` is
`Quotient (QuotientGroup.rightRel H)`: its points are the left cosets `H * g`,
so `Q_m = N_m \ GL_m`. Equality of the cosets of `g` and `g'` means
`g' * g⁻¹ ∈ H`. The chart uses the proved descent and representative
independence from the coordinates module.

## Measures and exact conclusions

After binding `chart`, the proposition quantifies over the explicit instance

```text
Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n + 1 + k))
```

and every actual `μ : Measure Q_(n+1+k+1)` with the published certificate

```text
IsCompatible (upperUnipotent (n + 1 + k + 1) F.Carrier)
  (generalLinearHaar F.Carrier (n + 1 + k))
  (unipotentHaar F.Carrier (n + 1 + k)) μ.
```

The two Haar measures are indexed by one less than their matrix rank.
`IsCompatible` means that `μ` is nonzero and regular, is invariant under
right translation, and satisfies the Weil integral formula and averaging
integrability for continuous compactly supported complex functions. The
right invariance instance is required by this existing predicate.

For every such measure the exact conclusion is

```text
Topology.IsOpenEmbedding chart ∧ Measurable chart ∧ μ (Set.range chart)ᶜ = 0.
```

Thus the chart is a homeomorphism onto an open range, is measurable for the
specified measurable structures, and the complement of its actual range has
`μ`-measure zero. No small-quotient compatibility or additive Haar input is
quantified, and no factorization, nonvanishing minor, Jacobian, normalization,
measure transfer, conullness or geometric property is assumed.

## Remaining proof obligations

The published coordinates module proves joint continuity and injectivity
and constructs a set-theoretic inverse on the actual range. Its inverse
continuity, openness of the range, and conullness remain to be proved. The
present module proves none of the three asserted conclusions, including
measurability for the specified product measurable structure.

A possible route is upper-unipotent/lower-triangular elimination on the
lower-right block, continuous Schur-complement recovery, and a proof that
vanishing lower-right corner minors form a Haar-null set, followed by
transfer of that null set to the compatible quotient. These are proposed
proof obligations, not hypotheses or established results of this module.
The parent disintegration task retains the right triangular Haar measure,
compact open volumes, determinant-weighted measure comparison with a positive
constant, integrability and integral transfer, and final assembly.
