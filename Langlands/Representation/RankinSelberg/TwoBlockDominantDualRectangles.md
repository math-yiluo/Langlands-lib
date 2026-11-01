# Signed exchange of the two dominant rectangles

This is internal derived support for the reversed-dual comparison in
Jacquet–Piatetski-Shapiro–Shalika (1983), Section 4.10(3), printed pp.419–420.
The original is registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The displayed original and reversed matrices, and the three-Weyl identity on
p.420, were read directly. No applicable source-specific erratum was found in
the checked registered index or project notes. The coordinate packaging and
measure theorems here are derived content, not a separately stated theorem
quoted from the source.

For any additive commutative group `K`, the additive equivalence
`signedReverseTranspose a b` sends a `b` by `a` matrix `X` to the `a` by `b`
matrix with entry `-X(l.rev,i.rev)`. Its explicit inverse has the same formula
with the dimensions exchanged. Entrywise involutivity of `Fin.rev` and
negation proves both inverse laws. The map is a homeomorphism whenever
negation is continuous.

Write `a=m 0+1` and `b=m 1+1`. The additive equivalence
`dualRectangleEquiv m j k` has source
`Rectangles (fun i => m i.rev) k j K` and target `Rectangles m j k K`.
Explicitly,

```text
(xD : b by j, yD : k by a)
  ↦ (signedReverseTranspose a k yD,
     signedReverseTranspose j b xD).
```

Thus the rectangles exchange positions as well as transposing and reversing
their coordinates. The inverse and continuity are proved directly. There is
no assumption that either `j` or `k` is positive.

For an arbitrary supplied additive Haar measure, the general
`measurePreserving_signedReverseTranspose` theorem assumes sigma-finiteness
and invariance under negation explicitly. Its proof compares the two measures
on measurable rectangular cylinders. The preimage reverses both finite index
sets and takes a negation preimage in every scalar coordinate. Negation
invariance and reindexing the two finite products give equality, including
zero dimensions. This proof adapts the private general-dimensional cylinder
argument in the published module `TwoBlockDualSectionJacquetProof`; it does
not reprove that module's section or Jacquet comparisons.

For every canonical `PadicField` in any field universe, these measure
hypotheses are synthesized for every supplied `AdditiveHaarMeasure`.
`measurePreserving_dualRectangleEquiv` then proves exact preservation from

```text
rectangularMeasure nu b j × rectangularMeasure nu k a
```

to

```text
rectangularMeasure nu a k × rectangularMeasure nu j b.
```

The proof composes preservation of the product swap with the two signed
transpose maps. The inverse preservation theorem uses the actual
homeomorphism. The Bochner-integral and `Integrable` equivalence theorems
follow from this measure-preserving equivalence for arbitrary functions and
independent target universes. No self-dual normalization is required and no
new measure is chosen.

This unit proves only the coordinate and supplied-Haar transport. The large
matrix comparison with `reversedMatrix`, the right factor `diag(I_N,w_c)`,
the determinant weights, lower-quotient geometry, scalar kernels and
determinant-slice transport remain separate obligations. It asserts no
convergence for arbitrary inputs and neither final dominant gamma/L target.

The canonical local instances have module-specific names so that this module
can be imported together with the other dominant scalar, rectangle and slice
helpers. This naming correction changes no instance value or mathematical
definition, statement or proof.
