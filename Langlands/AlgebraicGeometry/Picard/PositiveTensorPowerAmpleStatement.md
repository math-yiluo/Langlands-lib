# Ampleness under positive tensor powers and sheaf isomorphisms

`Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleStatement.{u}`
is a proposition about every scheme `X : Scheme.{u}`, every pair of actual
line bundles `L M : LineBundle X`, and every natural number `n`. It states

```text
0 < n → L.IsAmple →
  Nonempty (M.obj ≅ Langlands.Scheme.Modules.tensorPow L.obj n) → M.IsAmple.
```

The scheme and the line bundles are universally quantified inside the
proposition. There are no projectivity, noetherianity, separatedness,
residue-comparison, tensor-coherence, or rank-one-of-powers hypotheses.
`LineBundle X` already carries the local rank-one property for each of `L`
and `M`. The module on the right of the isomorphism is the published actual
sheaf tensor power; no choice of a tensor-power line-bundle constructor is
part of the statement.

## Source correspondence

The registered original is `stacks-ample-powers-restriction-quasiaffine-2026-10-24`,
*Stacks Project - Ample powers, closed restriction and quasi-affineness
(HTML snapshot 2026-10-24)*, directory SHA256
`03dddd39b5528263fbc3633f1545b8544e937bb29c9752ffe4a351bb6e093e9a`.
The precise location is `01PT.html`, [Lemma 28.27.2, tag 01PT](https://stacks.math.columbia.edu/tag/01PT),
the forward implication and its proof. The saved theorem, proof, and both
page comments were read. The comments concern the EGA reference and its
quasi-compactness convention. No source-specific erratum file is present
in the current Library's `notes/errata`.

The source states the equivalence between ampleness of an invertible sheaf
and ampleness of its `n`-th tensor power for `n ≥ 1`. Here `0 < n` is the
equivalent natural-number positivity condition. This proposition keeps the
forward implication and explicitly transports its conclusion across an
isomorphism of actual module sheaves. In ordinary sheaf language an
isomorphism `M ≅ L^{⊗n}` carries sections and their generation loci between
the two sheaves; its iterated tensor isomorphisms do the same for the powers
used to witness ampleness. Consequently the transported sections have the
same whole affine loci. This explains the extra universally quantified
`M` and the `Nonempty` isomorphism hypothesis: the caller may use any
existing line bundle with such an isomorphism, without constructing a
line-bundle structure on every tensor power. This transport formulation is
an internal packaging of the source implication, rather than a separate
claim that the source states that exact Lean signature. The converse of
the source equivalence is outside this proposition.

## Existing constructions and proof boundary

The import uses the published `LineBundle.IsAmple` from
`Langlands.AlgebraicGeometry.Picard.Ample`. That predicate asserts
compactness of `X` and, for every point, a section of a positive actual
tensor power whose entire generation open contains the point and is
affine. Its generation open is the largest open on which the
section-induced morphism from the structure sheaf is an isomorphism.
Thus affineness concerns the whole locus, not a chosen neighbourhood.

`Langlands.Scheme.Modules.tensorPow` is the right-associated sheafified
tensor power from `Langlands.AlgebraicGeometry.Modules.Tensor`; its zeroth
power is the structure sheaf and its successor is the tensor of the
original sheaf with the preceding power. In particular its first power
retains a final structure-sheaf tensor factor. The displayed isomorphism
uses these actual objects and allows their unit and associativity
isomorphisms to be handled in a future proof.

The source proof uses equality of the whole nonvanishing loci of a section
and its positive tensor power. A proof of this proposition must establish
the corresponding generation-open facts and the section transport for the
Library's actual tensors, or import independently proved comparisons to
the residue-field nonvanishing presentation together with the required
rank-one results. The conditional comparison in
`Langlands.AlgebraicGeometry.Modules.SectionResidueStatements` is not an
assumption of this proposition. This module defines the proof target only;
it proves neither the source implication nor isomorphism invariance of
ampleness and installs no axiom.

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean
4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
