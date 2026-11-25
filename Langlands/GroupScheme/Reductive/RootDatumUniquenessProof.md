# Proof of RootDatumUniquenessStatement

`Langlands.GroupScheme.rootDatumUniqueness.{u}` has exactly the published proposition
`Langlands.GroupScheme.RootDatumUniquenessStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Reductive.RootDatumStatement`.

Any two actual root data of a specified split maximal torus in a connected reductive field group admit a reindexing matching both roots and coroots.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
rootDatumUniqueness_of_weylImageFinite splitTorusWeylImageFinite
```

Apply the published coroot-comparison reduction to the unconditional finiteness theorem for the actual split-torus Weyl image. This discharges the sole structural premise.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.rootDatumUniqueness_of_weylImageFinite` in `Langlands.GroupScheme.Reductive.RootDatumCorootComparison`.
- `Langlands.GroupScheme.splitTorusWeylImageFinite` in `Langlands.GroupScheme.Torus.WeylImageFinite`.

This is an internal derived proof of the existing Library proposition.
The mathematical statement and its original-source interpretation remain those
of the published statement pair.
