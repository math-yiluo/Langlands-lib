# NYLL M301.005: the closed subgroup of the degree-`f` unramified extension

This file adapts one definition of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`29a3ec39fcabc17faa969f1c4c225a7cfd07555a00298e58daaa4b6fa6c7bb60`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines (declaration line) | Original name | Adapted name |
| --- | --- | --- | --- |
| M301.005 | 72–83 (73) | `ClassFormation.DegreeData.unramifiedExtensionOfDegree` | `Langlands.NYLL.ClassFormation.DegreeData.unramifiedExtensionOfDegree` |

## The objects

The definition uses only the actual published source objects. It introduces
no replacement degree datum, field, reduction map or kernel.

- `D : DegreeData G` (M010.002) is the source degree datum. Its field
  `D.degree : G →ₜ* ZHatMul` is a continuous surjective homomorphism to the
  multiplicative presentation of the profinite integers.
- `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field : ClosedSubgroup G` with finiteness of its residue quotient.
  `K.toSubgroup` (M010.023) is the underlying subgroup `K.field.toSubgroup`.
- `unramifiedDegreeHom D K f hf : K.toSubgroup →ₜ* Multiplicative (ZMod f)`
  (M301.001) is reduction modulo `f` composed with the normalized degree `d_K`.
  `unramifiedDegreeKernelWithin D K f hf : Subgroup K.toSubgroup` (M301.002)
  is its kernel.
- `ClosedSubgroup G` is Mathlib's bundled closed subgroup: a `Subgroup G`
  together with the field `isClosed'` asserting that its carrier is closed.

## Telescope

```lean
Langlands.NYLL.ClassFormation.DegreeData.unramifiedExtensionOfDegree
    {G : Type u} [Group G] [TopologicalSpace G]
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f) :
    ClosedSubgroup G
```

The source has the universe declaration `universe u` (source line 30) and the
section variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 34).
After these come the explicit binder `D`, the instance binder
`[IsTopologicalGroup G]` and the explicit binders `K`, `f`, `hf`, in source
order. All are retained. No hypothesis is added and none is removed.

## Construction

The subgroup is the image of the reduction kernel under the inclusion
`K.toSubgroup.subtype : K.toSubgroup →* G`:

```lean
toSubgroup := (unramifiedDegreeKernelWithin D K f hf).map K.toSubgroup.subtype
```

So it consists of the elements `g : G` that lie in `K.toSubgroup` and whose
normalized degree vanishes modulo `f`. In the source's terminology this is
the Galois group `G_L` of the unramified extension `L / K` of degree `f`: the
fixed field of that kernel.

The closedness field `isClosed'` is the source proof. It first uses `change`
to write the carrier as `Subtype.val '' (unramifiedDegreeKernelWithin D K f hf)`.
Then it applies Mathlib's `IsClosed.isClosedEmbedding_subtypeVal` to the
closedness `K.field.isClosed'` of `K`. The inclusion of a closed subset is a
closed embedding, so it is a closed map, and the image of the closed kernel is
closed. Closedness of the kernel in `K.toSubgroup` is the published M301.004
theorem `Langlands.NYLL.ClassFormation.DegreeData.unramifiedDegreeKernelWithin_isClosed`,
used by name exactly as in the source. Its type is the Prop-valued target
`unramifiedDegreeKernelWithin_isClosedStatement D K f hf`, which unfolds by
definition to the source proposition `IsClosed (unramifiedDegreeKernelWithin D K f hf : Set K.toSubgroup)`.

This module contains only the definition. The source theorems about this
subgroup are not part of it: Task 6082 submits them as later, separate
Prop-valued targets. These are M301.006 (membership), M301.007 (inclusion in
`K.toSubgroup`), M301.008 (the extension-subgroup identity) and M301.010
(normality).

## Modifications

Worker 452 makes these modifications:

- Extract only M301.005, with the source's noncomputable section (line 22),
  `open scoped Topology` (line 24), the universe declaration (line 30), the
  section `DegreeOnly` with its variable declaration (lines 32–34) and the
  namespace `DegreeData` (line 36). Omit all other source declarations. Narrow
  the module documentation to this definition.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`. The
  source line `open ClassFormation CyclicCohomology KummerTheory` (line 28) is
  omitted, because this declaration refers to no name from those namespaces
  outside its own namespace. The declaration name, docstring, telescope,
  result type and body, including both proof steps, are unchanged.
- Replace the source imports (`...Degree.FrobeniusFixedField`,
  `...Reciprocity.FiniteAbelianSubextension`, `...Reciprocity.NormTopology`)
  by the single published module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.U004.Proofs`.
  It contains the M301.004 proof used in the body. It transitively imports
  M301.001/.002, `DegreeData`, `FiniteResidueAbstractField` and Mathlib's
  `ClosedSubgroup`.
- Retain the original copyright, Apache-2.0 and author header. The Lean
  module documentation adds an explicit modification record.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
