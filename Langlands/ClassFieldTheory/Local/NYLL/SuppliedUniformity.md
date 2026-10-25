# The additive right uniformity of supplied local-field data

Worker 448 derives this adapter from the existing host construction
`Langlands.PadicField.TopologicalData.fieldT2` in
`Langlands/LocalField/Topology.lean`. Its full telescope is

```lean
Langlands.LocalClassField.NYLL.suppliedUniformSpace.{u}
    {p : ℕ} [Fact p.Prime] {F : Langlands.PadicField.{u} p}
    (TF : F.TopologicalData) : UniformSpace F.Carrier
```

The universe `u` is arbitrary. The only explicit argument is the supplied
realization `TF`; its algebraic field package and the primality certificate
are implicit. This declaration is explicit data and is not a global instance.
The `instance_reducible` attribute makes its value transparent to instance
elaboration without registering an instance.

## Construction

The body installs `TF.topology`, `TF.valuativeRel`, and `TF.localField` as
local instances, in that order. The field's additive commutative group comes
from `F.field`. Mathlib obtains the topological additive-group certificate
for this supplied topology from the local-field data. The body then installs
`IsTopologicalAddGroup.rightUniformSpace F.Carrier` locally and checks its
`IsUniformAddGroup` certificate with
`isUniformAddGroup_of_addCommGroup (G := F.Carrier)`. It returns that right
uniform structure. All these instance bindings are confined to the body.

For a topological additive group, Mathlib's generated
`IsTopologicalAddGroup.rightUniformSpace` uses the original
`TopologicalSpace` as its `toTopologicalSpace` field. Its uniformity is the
comap of the neighborhoods of zero along
`fun xy : F.Carrier × F.Carrier => xy.2 + -xy.1`.
Here those neighborhoods and that topology are exactly the ones in
`TF.topology`. The construction uses the supplied topology directly.

The topology identity and additive uniform-group property for this named
adapter will be exposed by separate compatibility targets. This pair
introduces only the uniform-space definition, with its local construction
certificate.

## Provenance and scope

This is internally derived host infrastructure, using the same local
right-uniformity and additive-group certificate as the published `fieldT2`
construction (original proof by Worker 6; shared interface by Worker 26).
The Mathlib implementation is in
`Mathlib/Topology/Algebra/IsUniformGroup/Defs.lean`, at commit
`5ed2965256430c3649e86755f9576b54eca72435`; the approved environment uses
Lean 4.34.0. The generated additive definition is inspected during
development because the source uses `to_additive`; its explicit
`UniformSpace.mk` term retains the original topological-space argument.

The NYLL namespace identifies its intended consumer. No external NYLL code
is copied or adapted in this pair. The adapter makes no reciprocity,
normalization, norm-kernel, or extension-valuation assertion.
