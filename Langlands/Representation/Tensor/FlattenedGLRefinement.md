# Tensor regrouping over a flattened GL Levi

Author: Worker 711.

`Langlands.FiniteTensor.flattenedTensorRegroupEquiv` specializes the published
rank-aware GL tensor comparison to a literal flattened block shape and moves
both actions to the actual flattened product Levi. This is an internal
algebraic construction from existing Library APIs.

Let `F : PadicField.{uF} p` have topological data `T`, let `B : BlockShape n`,
and let `Q : BlockRefinement B`. A factor family is
`A k : SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((B.flatten Q).size k) F.Carrier)`.
Set

```text
e := B.flattenBlockEquiv Q
h a := (B.flatten_size_flattenBlockEquiv Q a).symm
τ i j := (h ⟨i,j⟩).symm ▸ A (e ⟨i,j⟩).
```

The constructed representation equivalence has source
`(B.flatten Q).blockTensor (fun k => (A k).representation)` and target

```text
(FiniteTensor.external (fun i =>
  (Q i).blockTensor (fun j => (τ i j).representation))).comp
  (Geometric.flattenedLeviProductEquiv F.Carrier B Q).toMonoidHom.
```

Here `blockTensor` is the existing abbreviation for `FiniteTensor.external`.
The target is pulled back along the forward map from the flattened product
Levi to the nested product of inner Levis. Every rank cast is retained in
`τ`; its equality proof is the double inverse of the displayed flattened-size
equality, exactly as supplied by the published comparison. No ordering of
blocks is changed. The field and carrier universes remain independent, and
both tensor carriers have universe `uV` because the coefficient and index
universes are zero. The construction imposes no positive-rank, irreducibility,
admissibility or analytic hypotheses. It includes an empty outer shape when
`n = 0`.

The group identities `nestedLeviEquiv_flatten` and
`leviRefinementEquiv_flatten` identify the general refinement maps with the
existing flattened group maps. The first proof uses multiplicative-equivalence
extensionality and the published coordinate formulas, including actual matrix
rank reindexing. The second composes the first with `refinedLeviEquiv`.
`flattenedGroupComposite_apply` then cancels the inner group equivalence at
an arbitrary flattened element.

The private helper `cancelGroupPullback` starts with an actual equivalence
between actions pulled to a third group. It evaluates the intertwining
identity at the forward image of an element of the first group, cancels the
inverse there, and uses a supplied equality of composite group maps. It keeps
the underlying linear equivalence. The final construction applies this helper
to `FiniteTensor.glRefinementEquiv` with the preceding concrete group identity.
Its source and target actions are inferred from that published equivalence,
retaining the same carriers and rank transports.

The provenance is derived product-coordinate and representation algebra.
`Langlands.Group.GL.RefinementCoordinates` and
`Langlands.Representation.Geometric.FlattenedLevi` supply the actual group
maps and coordinate formulas.
`Langlands.Representation.Tensor.GLRefinement` supplies the rank-aware tensor
comparison, whose proof and constructions are imported unchanged. No new
external literature assertion is made. This module supplies algebraic
regrouping only; it does not establish analytic tensor reflection, support
extraction or normalized induction in stages.
