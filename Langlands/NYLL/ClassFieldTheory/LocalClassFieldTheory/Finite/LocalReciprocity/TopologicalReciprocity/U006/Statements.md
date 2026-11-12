# Openness and discreteness targets (M257.006–008)

This pair defines three unproved proposition targets from the pinned NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`.
They retain the original field units, norm subgroup and quotient topology.
All fields in these three targets are in `Type 0`, as in the source.

| Source unit and original name | Adapted target | Original lines |
| --- | --- | --- |
| M257.006, private `LocalClassFieldTheory.localNormSubgroup_isOpen_of_compatibleLocalField` | `Langlands.NYLL.PortInternal.M257.d006Statement` | 125–213 (signature 125–135) |
| M257.007, `LocalClassFieldTheory.localNormSubgroup_isOpen` | `Langlands.NYLL.LocalClassFieldTheory.localNormSubgroup_isOpenStatement` | 220–331 (signature 220–225) |
| M257.008, `LocalClassFieldTheory.normQuotient_discrete` | `Langlands.NYLL.LocalClassFieldTheory.normQuotient_discreteStatement` | 334–343 (signature 334–339) |

## Exact scope

`d006Statement` takes explicit `K L : Type`, then, in source order,
`NontriviallyNormedField K`, `NormedField L`, `NormedAlgebra K L`,
`CompleteSpace K`, `ValuativeRel K`, `IsNonarchimedeanLocalField K`,
`ValuativeRel L`, `IsNonarchimedeanLocalField L`, `FiniteDimensional K L`,
`IsGalois K L`,
`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`
and `IsIntegralClosure 𝒪[L] 𝒪[K] L`. It asserts
`IsOpen (localNormSubgroup K L : Set Kˣ)` in the units topology induced by the
given normed-field topology. The normed structures supply the field, algebra
and topology structures used here; no additional independent structures are
introduced. The integral-closure and valuation-extension hypotheses are retained.

The two public targets have the identical source telescope

```lean
(K L : Type) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
```

`localNormSubgroup_isOpenStatement` asserts
`IsOpen (localNormSubgroup K L : Set Kˣ)` in the native base-field unit topology.
It has no given topology or valuation on `L` and no normed-field structure as an
extra premise. `normQuotient_discreteStatement` asserts
`DiscreteTopology (NormQuotient K L)` for the quotient topology of the same unit
group by the same norm subgroup. Neither target has an abelian-Galois premise.
No field topology, valuation, or compatibility premise is omitted or added.

These definitions prove none of the three assertions. They introduce no
reciprocity map, finite-index hypothesis, or replacement discrete topology.

## Published dependencies and modifications

The file reuses `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` and
`Langlands.NYLL.LocalFieldTheory.NormQuotient` from the published
`NormQuotient.U001` and `NormQuotient.U002` definitions. The former is the range
of the published field norm on units, and the latter is `Kˣ` modulo that subgroup.
The quotient-topology bridge is the published source-local
`Langlands.NYLL.PortInternal.M257.d001`, from
`TopologicalReciprocity.U001.Definitions`. Its attribute is restored locally,
so no global topology or discreteness instance is exported. Its body is
Mathlib's `QuotientGroup.instTopologicalSpace` on this concrete quotient.
The local-field class is Mathlib's `IsNonarchimedeanLocalField`; opening the
NYLL namespace does not introduce a second class.

Worker 120 extracted the source signatures, prefixed namespaces, used the
inventory's stable private name `d006`, added `Statement`, changed each theorem
into a `def` returning `Prop`, and removed its proof. All explicitly written
binders, their order and hypotheses are retained, including the Type-zero
boundary despite the enclosing source section's unused universe declaration.
The full source imports are replaced by the published quotient topology and
Mathlib files supplying the local-field class, normed algebra, Galois,
valuation-extension and integral-closure structures. The source's local `open`
for `valuationSubring_isIntegralClosure_of_isIntegral` belongs only to its removed
M257.007 proof and is omitted. No patch or external draft is reused here.

A focused check verifies the three complete parameter telescopes, their
propositional bodies, and the explicit equality of the quotient topology to the
published local bridge. Thus these assertions need no Artin-map construction,
compactness/intersection proof, or class-formation imports. Those inputs remain
obligations for the later exact theorem proofs. Mathlib's
`QuotientGroup.discreteTopology` supplies discreteness from an *assumed* open
subgroup; it does not by itself prove this field's norm subgroup open. It is a
route for the later exact proof of M257.008 after M257.007 is proved.

## Provenance and attribution

The source commit is `fbd320cd8b1b06487c58227e92eb135794267709`; the original
module SHA-256 is
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`.
Source registration: `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The original copyright and author header, including assistance credit to
OpenAI Codex, is retained. The source is Apache-2.0, with unchanged license and
notice at `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`; their SHA-256 values
are `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The source NOTICE has no entry specific to this module. The extraction,
namespace, naming, proof removal and import changes are recorded above and in
the Lean header.
