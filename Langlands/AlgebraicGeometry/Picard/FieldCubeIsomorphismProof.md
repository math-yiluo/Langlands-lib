# The two-line-bundle isomorphism form of the geometric cube theorem

Author: Worker 1328. The specialization of the algebraic assembly follows
the carried draft by Worker 482 of the previous instance.

The module proves the exact published proposition:

```lean
theorem Langlands.AlgebraicGeometry.Picard.fieldCubeIsomorphism :
    Langlands.AlgebraicGeometry.Picard.FieldCubeIsomorphismStatement.{u}
```

The universe `u` is arbitrary. For every field `K : Type u`, the theorem
retains the three schemes over `Spec K`, all nine smooth, proper and
geometrically connected structure-morphism hypotheses, and the three
specified rational sections of the unchanged statement. For two actual
line bundles `L` and `M` on `(X ⨯ (Y ⨯ Z)).left`, it takes existence of
actual module-sheaf isomorphisms between their pullbacks along each of
`CubeFace.first`, `CubeFace.second` and `CubeFace.third`. It concludes
`Nonempty (L.obj ≅ M.obj)`. The three face witnesses need no compatibility,
and the conclusion does not specify their extension.

## Published dependencies

The proof imports these Library results by Lean name:

- `fieldCubeTriviality`, from `FieldCubeTrivialityProof`, proves
  `FieldCubeTrivialityStatement.{u}` unconditionally. After specialization
  to the field, schemes, nine geometric hypotheses and three rational
  sections, it detects triviality of any actual line bundle from
  triviality of its three face pullbacks.
- `locallyFreeRankOneIffTensorInvertible`, from `LocalComparisonProof`,
  identifies local freeness of rank one with tensor invertibility for
  every actual module sheaf on the ambient scheme.
- `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`, from
  `Modules.PullbackTensorProof`, proves that the canonical comparison
  between pullback of the explicit sheaf tensor and tensor of pullbacks
  is an isomorphism for every scheme morphism.
- `lineBundleIsoOfThreePullbackComparisons`, from
  `CubeIsomorphismAssembly`, constructs an actual isomorphism from three
  pullback comparisons under these tensor and triviality principles.

All three proof prerequisites are discharged by the imported theorems.
The final declaration has exactly `FieldCubeIsomorphismStatement.{u}` as
its type. The target statement and its imported Lean/Markdown pairs are
preserved.

## Implemented proof

The Lean proof introduces the field, schemes, geometric hypotheses,
sections and line bundles from the target. Pattern matching on each
`Nonempty` hypothesis gives the three actual face isomorphisms
`e₁`, `e₂` and `e₃`. It calls
`lineBundleIsoOfThreePullbackComparisons` with the three actual face
morphisms, the two published tensor proofs and the specialization of
`fieldCubeTriviality`, then wraps the resulting isomorphism in `Nonempty`.

The imported algebraic assembly implements the following tensor argument.
Local rank one of `M.obj` gives an existential right tensor inverse `N`,
with `M.obj ⊗ N ≅ O`. Braiding also gives `N ⊗ M.obj ≅ O`.
Tensor invertibility of `L.obj` and `N`, transported through
`localizedTensorIso`, proves that the explicit sheaf tensor
`tensorObj L.obj N` is a line bundle, called `difference`.

For each face, `pullbackTensorInverseTrivialization` composes the
canonical tensor comparison, the tensor of the given face isomorphism
with the identity on the pullback of `N`, the inverse tensor comparison,
the pullback of the chosen inverse isomorphism, and `pullbackUnitIso`.
This trivializes the actual pullback of `difference` on that face.
The published geometric cube theorem makes `difference` itself trivial.
The assembly then composes actual monoidal isomorphisms

`L.obj ≅ L.obj ⊗ O ≅ L.obj ⊗ (N ⊗ M.obj) ≅
(L.obj ⊗ N) ⊗ M.obj ≅ O ⊗ M.obj ≅ M.obj`.

The fourth arrow uses `localizedTensorIso` and the cube trivialization.
These constructions use classical choice inside the published assembly.
The final result is an actual module-sheaf isomorphism asserted to exist.
The argument obtains the tensor inverse internally and uses the existing
line bundles, face maps and pullback functors throughout.

## Provenance and sources

This is an internal tensor-algebra corollary of J. S. Milne,
*Abelian Varieties*, corrected January 2, 2022 author version of the
1986 chapter, Theorem 6.1 on printed/PDF page 8. Milne states the
triviality theorem for one invertible sheaf; the two-line-bundle form is
the derived comparison explained above. The statement companions explain
how the retained smooth proper geometrically connected hypotheses agree
with the source's variety conventions on page 2. The geometric proof is
imported from `FieldCubeTrivialityProof`; this module implements its
tensor-algebra corollary.

The original conventions on page 2, Theorem 6.1 and its proof and descent
Lemma 6.2 on pages 8–9, and the complete retained author errata were read.
None of the listed errata changes Theorem 6.1.

- Registered source `milne-abelian-varieties-1986-author-2022`;
  retained file
  `literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`;
  SHA-256
  `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`;
  locators: pages 2 and 8–9, especially Theorem 6.1.
- Registered source `milne-abelian-varieties-1986-errata-2026-10-25`;
  retained file
  `literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`;
  SHA-256
  `e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`;
  locator: complete author errata list.
