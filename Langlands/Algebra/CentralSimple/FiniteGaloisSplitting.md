# Finite Galois matrix splitting of central simple algebras

For every field `K : Type u` and unital ring `A : Type u` with
`[Algebra K A] [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]`,
this module constructs a finite Galois extension of `K` in the same universe
and an actual matrix splitting chart over that extension. All declarations
are in `Langlands.CentralSimple`. There is no restriction on characteristic.

The matrix size is the public `reducedDegree K A`, defined in
`Langlands.Algebra.CentralSimpleScalarExtension` as
`Nat.sqrt (Module.finrank K A)`. The proved specification
`finiteGaloisSplittingChart_spec` gives

```text
0 < reducedDegree K A
Module.finrank K A = reducedDegree K A * reducedDegree K A.
```

The public constructors are:

- `finiteGaloisSplittingIntermediateField K A`, a
  `FiniteGaloisIntermediateField K (SeparableClosure K)`;
- `finiteGaloisSplittingField K A : Type u`, its underlying field, with public
  `Field`, `Algebra K`, `FiniteDimensional K` and `IsGalois K` instances;
- `finiteGaloisSplittingChart K A`, an actual algebra equivalence
  from `finiteGaloisSplittingField K A ⊗[K] A` to
  `Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A))
  (finiteGaloisSplittingField K A)` over the chosen splitting field.

`exists_finiteGalois_splitting K A` packages the positive integer, square
dimension, field type and structures, finite dimension, Galois property and
`Nonempty` actual equivalence into one proposition. The constructors above
provide the data directly. They are classical choices; no canonical chart
or minimal splitting field is claimed.

The construction first uses the proved `separableClosureChart K A` from
`Langlands.Algebra.CentralSimple.SeparableClosureChart`. This constructs a chart
over the actual separable closure from the finite-dimensional central-simple
hypotheses. Its proof uses preservation of central simplicity after field
extension and the classification over a separably closed field. The latter
uses Wedderburn–Artin and Jacobson–Noether: a nontrivial central division algebra
would contain a nonscalar separable element, whereas every such element over a
separably closed field is a scalar.

The actual separable closure is Galois over `K`. Applying
`finiteGaloisMatrixChartField` and `finiteGaloisMatrixChart` from
`Langlands.Algebra.CentralSimple.FiniteGaloisDescent` adjoins the finitely many
matrix entries of the images of a finite `K`-basis of `A`, takes their normal
closure inside the separable closure, and descends the chart to that finite
Galois intermediate field. Entry containment extends by the basis expansion.
Tensor-inclusion compatibility and flatness prove injectivity of the descended
homomorphism; equal finite dimensions prove surjectivity. The reduced-degree
specifications supply positivity and the original dimension identity.

The source is J. S. Milne, *Algebraic Groups*, corrected reprint (2022),
Chapter 24d, Theorem 24.19 and Propositions 24.21–24.22, printed pages 521–522
(PDF pages 532–533), followed by the finite Galois splitting step in the proof
of Theorem 24.23, printed page 522 (PDF page 533). The registered source
`milne-2022-algebraic-groups` has SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The complete retained author errata snapshot for the 2022 reprint contains
no correction to these passages. Milne's footnote 3 calls the matrix size the
reduced degree; his degree is the full dimension. The tensor factors here use
the standard extension-of-scalars order.

The splitting field, chart and preservation of central simplicity are proved
constructions, with no splitting hypothesis, scalar-extension simplicity
hypothesis, or supplied maximal separable subfield. The theorem works in every
universe `u` and in positive characteristic, including imperfect base fields.
