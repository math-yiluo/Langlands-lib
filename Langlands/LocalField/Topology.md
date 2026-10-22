# Hausdorffness of a supplied p-adic field realization

Original proof: Worker 6. Shared interface and consumer migration: Worker 26.

For every prime `p`, every `F : PadicField.{u} p` in arbitrary carrier
universe `u`, and every supplied `T : F.TopologicalData`,
`Langlands.PadicField.TopologicalData.fieldT2` has exactly the type

```lean
letI := T.topology
T2Space F.Carrier
```

Use `letI := T.topology` followed by `letI := T.fieldT2` to install the
certificate locally. The declaration is not an instance. Its only inputs are
the existing primality instance, algebraic field package, and supplied
realization. It introduces no new topology, norm, valuation normalization or
field hypothesis.

## Proof and provenance

This is an extraction of the identical private `fieldT2` proofs previously
in `Langlands.Group.GL.PadicBlocks` and
`Langlands.Group.GL.PadicUpperUnipotent`. The proof body and full telescope
are retained. It installs `T.topology`, `T.valuativeRel` and `T.localField`,
then the additive group's right uniform structure and its
`IsUniformAddGroup` certificate. Mathlib supplies the compatible valued-field
structure and separation, yielding Hausdorffness for the selected topology.
The right uniform structure retains the supplied underlying topology.

The audited Mathlib interfaces at commit
`5ed2965256430c3649e86755f9576b54eca72435` are:

- `Mathlib.NumberTheory.LocalField.Basic`: the existing
  `IsNonarchimedeanLocalField` and topological division-ring certificates.
- `Mathlib.Topology.Algebra.IsUniformGroup.Defs`:
  `IsTopologicalAddGroup.rightUniformSpace` and
  `isUniformAddGroup_of_addCommGroup`.
- `Mathlib.Topology.Algebra.Valued.ValuativeRel`: the low-priority `Valued`
  instance obtained from a compatible uniform additive group and
  `IsValuativeTopology`.
- `Mathlib.Topology.Algebra.Valued.ValuedField`: `ValuedRing.separated`;
  the topological additive-group separation interfaces give `T2Space`.

These interfaces are already imported by `LocalField.Definitions`.
No mathematical generalization or comparison with the canonical realization
is asserted here. This intrinsic certificate is internal construction
infrastructure; the GL consumers retain their original literature references
and conventions.

## Module and declaration migration

The extraction uses Library base
`a6142598ca59c1c7c4408d715a4ae77cfe7469bc`. The three original GL pairs
are byte-identical to the development baseline
`30ceb5a0d89d8094c1663fc19f35416519b9a125`, which the workspace matched
before restoring this extraction.

| Previous location or name | Shared location or retained interface |
| --- | --- |
| Private `fieldT2` in `Group.GL.PadicBlocks` | `LocalField.Topology`, public `PadicField.TopologicalData.fieldT2` |
| Private `fieldT2` in `Group.GL.PadicUpperUnipotent` | The same shared certificate |
| Field separation preparation in `Group.GL.Padic.generalLinearT2Space` and `generalLinearLocallyCompactSpace` | Local use of `T.fieldT2` |
| `Group.GL.Padic` imports `Group.GL.Basic` and `LocalField.Canonical` | Both imports retained; `LocalField.Topology` added |
| `Group.GL.PadicBlocks` and `Group.GL.PadicUpperUnipotent` imports | Retained; the shared certificate is available through `Group.GL.Padic` |
| All public topologies, certificates, maps and canonical abbreviations in the three GL modules | Names, full types, selected topologies and underlying maps retained |

All original module paths remain available. Existing direct consumers
`Group.GL.Maps`, `Group.GL.NormalizedCharacter`, `Group.GL.RankMaps`,
`Group.GL.BlockModulus` and `Representation.Classification.Supercuspidal`
keep their imports and public interfaces. Frozen dependent constructions
are not edited by this extraction. The canonical local-field construction and
normalization modules are unchanged.
