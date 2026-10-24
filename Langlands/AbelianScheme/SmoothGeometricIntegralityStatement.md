# Smooth geometrically connected schemes over fields

`Langlands.AbelianScheme.SmoothGeometricIntegrality` is a universe-polymorphic
`Prop`-valued definition. For every field `K : Type u`, every scheme
`X : Scheme.{u}`, and every structure morphism `p : X ⟶ Spec (CommRingCat.of K)`,
it asserts

```text
Smooth p → GeometricallyConnected p → GeometricallyIntegral p.
```

All three predicates are Mathlib's actual morphism predicates. This file states
the implication and supplies no proof. It imports only Mathlib; no rigidity
statement or group-scheme result enters the target.

## Quantifiers and conventions

Mathlib's `geometrically` tests a property after every morphism
`Spec L ⟶ Spec K`, where `L : Type u` is a field, and on every scheme fitting
into the corresponding pullback square. A morphism of these affine spectra
corresponds to a unital field homomorphism `K → L`, hence to a field extension.
Thus `GeometricallyConnected p` supplies `ConnectedSpace` on every such base
change, and `GeometricallyIntegral p` asserts `IsIntegral` on every such base
change. The universe parameter is arbitrary; the field-extension test uses
the same universe as Mathlib's scheme category.

In Lean, `ConnectedSpace` includes nonemptiness. Consequently the empty scheme
cannot satisfy the hypothesis, and no additional nonemptiness hypothesis or
identity section is needed. `IsIntegral` means reduced and irreducible,
including nonemptiness through irreducibility.

## Original sources and derivation

The provenance is derived: combine the following original Stacks Project
results for each field extension. The source statements and proofs were read
directly. There is no project errata note for either registered source.

1. [Tag 056T](https://stacks.math.columbia.edu/tag/056T), Lemma 33.25.4,
   states that a smooth scheme over a field is geometrically regular, normal,
   and reduced. Its proof uses regularity and regular-implies-normal.
   This is retained in `056T.html` under literature ID
   `stacks-global-functions-field-and-fibre-criterion-2026-10-23`, source SHA256
   `c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`.
2. The supplementary original pages are retained under literature ID
   `stacks-smooth-connected-integral-2026-10-24`, source SHA256
   `5374d7e59f547f5114ea9217b3fdfc3c6d0b3f9cf7ab3ed0f35da7163ba7f794`.
   [Tag 01VB](https://stacks.math.columbia.edu/tag/01VB), `01VB.html`,
   states stability of smoothness under base change.
   [Tag 056S](https://stacks.math.columbia.edu/tag/056S), `056S.html`,
   Lemma 33.25.3 and its proof, gives regularity and local Noetherianity for
   a scheme smooth over a field. [Tag 0569](https://stacks.math.columbia.edu/tag/0569),
   `0569.html`, gives normality of regular schemes.
3. In that supplementary source, [Tag 033N](https://stacks.math.columbia.edu/tag/033N),
   `033N.html`, Lemma 28.7.7, decomposes a locally Noetherian normal scheme
   into a disjoint union of integral normal schemes.
   [Tag 0357](https://stacks.math.columbia.edu/tag/0357), `0357.html`,
   Lemma 28.7.5 and its proof, explains that the irreducible components are
   open and disjoint under the local finiteness condition supplied here by
   local Noetherianity.
   [Tag 033O](https://stacks.math.columbia.edu/tag/033O), `033O.html`,
   Remark 28.7.8, records the resulting connectedness-to-integrality implication.
   We use it for nonempty schemes, as required by Lean's connectedness convention.

For any field extension `L/K`, the pullback `X_L` is smooth over `L`, hence
locally Noetherian, regular, and normal. Its nonempty connectedness is supplied
by `GeometricallyConnected p`. In the disjoint open decomposition from Tag 033N,
connectedness permits only one nonempty component. Thus `X_L` is integral.
Applying this argument to every field-valued base change gives exactly
`GeometricallyIntegral p`; the argument does not test only an algebraic closure.

## Scope and proof boundary

Quasi-compactness is unnecessary: the argument uses local Noetherianity, which
smoothness over a field already supplies. The target therefore also covers the
requested finite-type case with `QuasiCompact p`. There is no perfectness,
algebraic-closedness, characteristic, separation, properness, or group-structure
restriction. Regularity, normality, reducedness and irreducibility are
intermediate consequences in the source derivation, not additional hypotheses.

A separate proof must establish this exact proposition from the published
interface. This statement contribution neither assumes nor implements those
intermediate consequences.
