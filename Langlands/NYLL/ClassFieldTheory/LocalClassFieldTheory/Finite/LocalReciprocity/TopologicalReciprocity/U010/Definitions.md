# Finite algebraic and topological Galois abelianizations

`Langlands.NYLL.LocalClassFieldTheory.topologicalAbelianization_finite_equiv`
is the multiplicative equivalence between the algebraic abelianization and
the topological abelianization of the actual finite automorphism group.
Its full elaborated interface is

```lean
(K L : Type) → [Field K] → [Field L] → [Algebra K L] →
  [FiniteDimensional K L] →
  Abelianization (Gal(L / K)) ≃* TopologicalAbelianization (Gal(L / K))
```

Both fields lie in universe zero, exactly as in the source. This is a
multiplicative equivalence; no continuity fields are asserted in this unit.
The automorphism group has its native Krull topology. Mathlib's
`krullTopology_discreteTopology_of_finiteDimensional` supplies discreteness.
The algebraic abelianization quotients by the commutator, while the topological
abelianization quotients by its topological closure. These subgroups agree in
a discrete group, and `QuotientGroup.quotientMulEquivOfEq` supplies the actual
quotient equivalence using the same equality orientation as the source.

## Source correspondence and Mathlib reuse

| Source unit and declaration | Adaptation or replacement |
| --- | --- |
| M257.009, private `LocalClassFieldTheory.commutator_topologicalClosure_eq`, lines 353–359 | Existing Mathlib `IsClosed.closure_eq`, specialized using `isClosed_discrete`, and `SetLike.coe_injective` |
| M257.010, `LocalClassFieldTheory.topologicalAbelianization_finite_equiv`, lines 361–368 | `Langlands.NYLL.LocalClassFieldTheory.topologicalAbelianization_finite_equiv` |

The exact pinned original is
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, SHA-256
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`.
The original registration is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the available project notes.

The Mathlib replacement of M257.009 uses precisely that source helper's
premises: in a discrete topological group every subset is closed, so
`IsClosed.closure_eq` applies to the commutator's carrier. The carrier of
`Subgroup.topologicalClosure` is definitionally the ordinary set closure,
as recorded by Mathlib `Subgroup.topologicalClosure_coe` in
`Mathlib/Topology/Algebra/Group/Subgroup.lean`. `SetLike.coe_injective`
converts the existing set equality into the required subgroup equality.
Thus the source helper is reused from existing general Mathlib facts and
is not duplicated as a new theorem or assumed as an extra premise.

## Parameters, modifications and focused verification

The original enclosing section telescope is retained verbatim. Its supplied
`ValuativeRel K`, `TopologicalSpace K`, `IsNonarchimedeanLocalField K` and
`IsGalois K L` instances do not occur in this definition's elaborated type
or body, so Lean omits them, exactly as in the original declaration.
This was checked against a verbatim extraction of the original M257.009–010
with the original enclosing telescope in a private diagnostic namespace:
both complete types agree, and an equality between the two fully applied
constant functions is accepted by `rfl`. The replacement changes only the
proof certificate of the same subgroup equality; the quotient equivalence
is definitionally the source construction.

The successful focused check compiled with no other NYLL module. The imports
are `Mathlib.FieldTheory.KrullTopology`,
`Mathlib.Topology.Algebra.Group.TopologicalAbelianization` and
`Mathlib.NumberTheory.LocalField.Basic`. The first two are original imports;
the last retains the source's local-field section vocabulary. All original
NYLL imports and unused Mathlib imports are omitted. This establishes that
the preceding Artin construction, norm openness/discreteness and
M257.001–008 are not prerequisites of this isolated data definition.
The retained source private M257.009 is resolved by the named Mathlib reuse
above. These import reductions are supported by a successful focused build,
rather than inferred only from the inventory's conservative scheduling edges.

Other changes are the `Langlands.NYLL` namespace prefix, a prominent
modification notice, and the focused module prose. No global instances are
introduced. The later reciprocity equivalence and Artin maps remain separate
construction and proof obligations; this data does not supply them.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The unchanged Apache-2.0 [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) accompany this
subset under `licenses/NYLL/`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
NOTICE has no source-specific entry for this file. Worker 120 made these
namespace/import and Mathlib-certificate changes on 9 November 2026.
No earlier draft or patch10 adaptation is incorporated.
