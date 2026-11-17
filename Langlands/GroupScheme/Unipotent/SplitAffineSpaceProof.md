# Split unipotent groups are affine spaces

Worker 315.

`Langlands.GroupScheme.splitUnipotentAffineSpaceStatement.{u}` proves exactly
the published proposition
`Langlands.GroupScheme.SplitUnipotentAffineSpaceStatement.{u}`. It has no
additional hypotheses. For every field `k : Type u`, every `n : ℕ` and every
group scheme `H` over `Spec k`, affineness of `H` and a split series of length
`n` give a nonempty type of isomorphisms

\[
  H \simeq_k \mathbb A_k^n
\]

of underlying schemes. The isomorphisms live in `Over (Spec k)`. No assertion
that they preserve the group operation is made.

## Source and provenance

The unchanged statement is in
[`SplitAffineSpaceStatement`](SplitAffineSpaceStatement.md). Its original
source is James S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (Cambridge University Press, 2017), registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The relevant locations are 14.61, 14.62 and 14.66, printed p.299
(one-based PDF p.315), and the Chapter 14 affine convention, printed p.279
(PDF p.295). These pages were read from the registered original PDF.

Milne 14.66 identifies the underlying scheme of a split unipotent algebraic
group of dimension `n` with affine `n`-space. The target expresses the
dimension by the length of a series with one-dimensional additive
quotients; the published statement Markdown explains this correspondence.
The letter used for the group in the second sentence of 14.66 is a
typographical inconsistency. The retained official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, Chapter 14 entry, has no
correction to 14.61, 14.62 or 14.66.

The proof below follows the induction and torsor-trivialization route
recorded in the task and the statement Markdown, using a published product
decomposition. The coordinate comparison and finite product lemmas are
internal derived constructions from Yoneda, the existing Library
affine-space coordinate equivalence, and finite tuple concatenation.
They do not assert additional results from Milne.

## Imports and coordinate constructions

The proof imports the statement without changing it. It also imports:

- [`Rational.SplitSeriesProductDecomposition`](../Rational/SplitSeriesProductDecomposition.md),
  for the one-step product decomposition of an affine group with a split series.
- [`Rational.SplitSeriesUnipotent`](../Rational/SplitSeriesUnipotent.md),
  for the zero-dimensional vector coordinates of a group with a length-zero series.
- [`MatrixRepresentation.SchemeAction`](../MatrixRepresentation/SchemeAction.md),
  for `coefficientSpace`, `coefficientPointEquiv` and their coordinate laws.
- Mathlib's `Mathlib.Logic.Equiv.Fin.Basic`, for `Fin.appendEquiv`.

For `R : CommRingCat.{u}`, the existing
`MatrixRepresentation.coefficientSpace (Fin n) R` is definitionally

```lean
Over.mk (𝔸(ULift.{u} (Fin n); Spec R) ↘ Spec R).
```

Its morphisms from an arbitrary test scheme `T` over `Spec R` correspond
bijectively to `Fin n → Γ(T.left, ⊤)` through `coefficientPointEquiv T`.
The coordinate of a composite is obtained by pulling back the corresponding
global section.

The new helper namespace is `Langlands.GroupScheme.SplitAffineSpace`:

- `isoOfCoordinates` takes any `X : Over (Spec R)` with equivalences
  `(T ⟶ X) ≃ (Fin n → Γ(T.left, ⊤))` natural in every test scheme `T`.
  Composing these equivalences with the inverses of `coefficientPointEquiv`
  gives natural bijections of represented functors. `Yoneda.ext` constructs
  an isomorphism from `X` to `coefficientSpace (Fin n) R`. The inverse laws
  are the equivalence inverse laws, and naturality is checked by the
  coordinate pullback formula.
- `vectorIso` applies this construction to the natural multiplicative
  equivalences in `RelativeRoot.IsVectorGroupOfDimension V n`, forgetting
  their multiplicative structure and removing the `Multiplicative` type
  tag. It gives the underlying scheme isomorphism in every dimension,
  including zero, over any commutative ring.
- `productIso` identifies
  `coefficientSpace (Fin n) R ⊗ coefficientSpace (Fin m) R` with
  `coefficientSpace (Fin (n + m)) R`. The cartesian product universal
  property gives pairs of morphisms on every test scheme; the two
  affine-space coordinate equivalences give pairs of coordinate vectors;
  `Fin.appendEquiv n m` concatenates them. Naturality is verified separately
  on the first and second coordinate blocks by `Fin.addCases`.
  `isoOfCoordinates` then gives the required isomorphism over `Spec R`.

## Induction proving the target

The theorem introduces `k` and proceeds by induction on the series length.

At length zero,
`RelativeRoot.HasSplitSeries.isVectorGroupOfDimension_zero` supplies the
natural zero-dimensional vector coordinates. `vectorIso` identifies the
underlying scheme with the specified affine zero-space.

At length `n + 1`, the affineness hypothesis is installed as an instance.
`SplitSeriesDecomposition.HasSplitSeries.exists_iso_tensor` supplies group
schemes `K`, `V`, an isomorphism `e : K.X ⊗ V.X ≅ H.X`, a split series of
length `n` for `K`, a one-dimensional vector-group witness for `V`, and
affineness of `K`. The imported decomposition constructs a section of the
quotient and identifies the product with `H` by multiplication.

The induction hypothesis identifies `K.X` with affine `n`-space.
`vectorIso` identifies `V.X` with affine one-space. Their tensor product
is an isomorphism of the two products in `Over (Spec k)`. Composing
`e.symm`, this tensor product isomorphism, and `productIso _ n 1` gives the
required isomorphism with affine `(n + 1)`-space. The theorem returns its
`Nonempty` witness.

The proof works at the arbitrary universe parameter `u`, uses no
connectedness or field restrictions beyond the exact published target,
and adds no axioms.
