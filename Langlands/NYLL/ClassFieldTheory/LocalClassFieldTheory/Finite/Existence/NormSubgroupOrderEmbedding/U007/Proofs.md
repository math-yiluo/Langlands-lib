# Abstract fixed-field relative norm in base units

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement`
by the theorem of the same name without the `Statement` suffix.
The target is imported unchanged from `NormSubgroupOrderEmbedding.U007.Statements`.

## Statement and scope

Let `K : Type` be a field, let `H` be a closed subgroup of
`intrinsicAbsoluteGalois K`, and let
`hH : H.toSubgroup ≤ (intrinsicAbstractBase K).toSubgroup`.
Assume the relative coset quotient
`(intrinsicAbstractBase K).toSubgroup ⧸ extensionSubgroup (intrinsicAbstractBase K) H hH`
is finite, and that the actual fixed field
`E := abstractFixedField K (SeparableClosure K) H` is finite dimensional and
Galois over `K`. For every `x : Eˣ`, the conclusion is equality in
`Additive Kˣ`:

```lean
(baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
  (relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
    H hH (abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H (Additive.ofMul x))) =
  Additive.ofMul (normUnits K E x)
```

The theorem keeps every source binder in its original order: explicit `K`,
its field instance, explicit `H` and `hH`, the three finiteness/Galois
instances, and explicit `x`. The ground field remains in universe zero.
No local-field hypothesis or supplied norm equality is added.

## Implemented proof

Unfold the published proposition. Apply injectivity of the canonical
base-unit equivalence and its `apply_symm_apply` law. Subtype, additive and
unit extensionality reduce the goal to equality of field values in
`SeparableClosure K`.

The published theorem
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_val_of_isGalois`
(M300.006), imported from `NormSubgroupOrderEmbedding.U006.Proofs`, identifies
the relative-norm value with `algebraMap K (SeparableClosure K) (Algebra.norm K x)`.
The next equality is `rfl`: `normUnits K E` is definitionally
`Units.map (Algebra.norm K)`, so its underlying field value is the algebra
norm. Finally, use the symmetry of the published theorem
`Langlands.NYLL.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val`
(M096.002), imported from
`SeparableUnitsNorm.BaseUnits.U002.Proofs`, at `normUnits K E x`.
This proves the exact target directly, without reproving either imported
comparison theorem.

## Provenance and modifications

Adapted by Worker 324 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`,
M300.007, lines 201–232 (signature 201–215, proof 216–232), with section
binders from line 32. The readable source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`.
Its SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.
It belongs to registered sources `external-lean-reuse-snapshots-2026-10-21`
and `nyll-classfieldtheory-fbd320cd-supplement`.

The adaptation prefixes the namespace by `Langlands.NYLL`, uses three
focused Library imports, moves the section binders into the theorem, and
states its type using the already published proposition. The proof adds
one unfold of that proposition and replaces the source's
`normUnits_apply_coe` rewrite with definitional equality. The source's
extensionality steps, M300.006 invocation, and final base-unit value
comparison are preserved. Unused namespace openings and unrelated source
declarations are omitted; module documentation and the theorem docstring
are adapted to this focused proof.

The original Apache-2.0 copyright and author header is retained verbatim.
The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained
without changes; their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
