# General linear groups over every finite p-adic extension

Author: Worker 6. Shared Hausdorff-certificate extraction: Worker 26.
This is a construction group for task
974e7b2e-4779-4b03-a8a1-6b81962d310c, revision 2.

The carrier of every group in this file is the actual
`Langlands.GeneralLinear n F.Carrier` from `Basic.lean`. Here `p` is any prime,
`F : PadicField p` is any of the accepted algebraic finite extensions, in an
arbitrary universe, and `n` is any natural number. No normality, unramifiedness,
or degree restriction is imposed. Thus all requested positive ranks are covered.

For a supplied `T : F.TopologicalData`, `generalLinearTopology` uses the topology
of matrix units induced by `T.topology`. The next three proved certificates provide
explicit certificates of a topological group, Hausdorffness, and local compactness
for precisely this topology. They install `T.topology`, `T.valuativeRel`, and
`T.localField` locally and use existing Mathlib instances. No desired conclusion
is included as a new hypothesis.

The proofs use the local-field instances already certified by `T`. Field
Hausdorffness is supplied by `T.fieldT2` from
[`LocalField.Topology`](../../LocalField/Topology.md). That shared certificate
retains the original proof using the compatible right uniform structure,
its `IsUniformAddGroup` certificate, and Mathlib's valued-field separation.
Both `generalLinearT2Space` and `generalLinearLocallyCompactSpace` install
this certificate locally for exactly `T.topology`. For local compactness, the proof
also explicitly transfers the finite function-space instance to `Matrix`;
this avoids relying on typeclass search to unfold that type alias. The finite
matrix space is a finite product of the Hausdorff locally compact field. Mathlib
embeds the unit group as a closed subset of the product of this matrix space and
its multiplicative opposite, by sending a unit to its value and inverse. This
gives local compactness and Hausdorffness. The same unit-group topology makes
multiplication and inversion continuous.

`generalLinearDeterminant` and `generalLinearScalar` specialize the continuous
homomorphisms from `Basic.lean` with the selected field topology. They still have
the usual matrix determinant and scalar matrix as their underlying functions.
Install `letI := T.topology` when using these maps. To use only the group
topology and its properties, one can install the four explicit group structures
in order:

```lean
letI := T.generalLinearTopology n
letI := T.generalLinearTopologicalGroup n
letI := T.generalLinearT2Space n
letI := T.generalLinearLocallyCompactSpace n
```

The four `canonicalGeneralLinear...` abbreviations apply the same constructions
to the accepted `F.canonicalTopologicalData`. They require the algebraic field
alone. They introduce no global topology instance on the field, and make no
identification between the spectral norm and the residue-normalized absolute
value.

This is an internal specialization of the accepted local-field constructors and
Mathlib's existing matrix-unit topology. The mathematical setting agrees with
Bernstein–Zelevinsky (1977), Sections 2.1–2.2, printed page 446: `GL(n,F)` with
its natural locally compact topology. The original passage was read.

Exact project dependencies:

- `Langlands.LocalField.Definitions`, artifact
  `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1, publication commit
  `1fe07fd211e579cc430734fd96ce959aadb7663d`.
- `Langlands.LocalField.Canonical`, artifact
  `c342ec21-e5ee-4ba4-aec6-b4c1b1e2b629`, version 1, publication commit
  `9db46907db3181b0c1dfd287b8ab2f1f02054cab`.
- `Langlands.Group.GL.Basic` is the companion module within this construction
  group.

Both local-field dependencies were freshly fetched and verified accepted,
public, published, and current at Library commit
`d0f5322f745425b08ae8e72c1031206f45cb049e`. Their complete effective pairs and
review/validation receipts were read. The pinned environment is Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

Nonarchimedeanness of these general linear groups and the resulting compact-open
bases are not supplied by this construction group. The generic compact-open theorem is
already published, but its `NonarchimedeanGroup` hypothesis must be discharged
for the actual matrix groups before applying it.

The source locator is `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
Sections 2.1–2.2, printed page 446. The companion `Basic.md` also records
Henniart (2002), Section 2.5, printed pages 594–595, for the determinant
convention.

The extraction adds the `Langlands.LocalField.Topology` import and retains
the `Basic` and `Canonical` imports. Every public declaration name and full
type in this module, including the topologies, continuous maps and canonical
abbreviations, is retained. The shared module's
[migration map](../../LocalField/Topology.md#module-and-declaration-migration)
records the three GL consumers and preserved import paths.
