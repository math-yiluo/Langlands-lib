# NYLL M010.021–025: finite-residue abstract-field data

This module extracts five data commands from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, lines
165–198, at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The source file SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

All public names below have prefix `Langlands.NYLL.ClassFormation.DegreeData`.
The imported `Fields.Definitions` supplies the actual source `DegreeData`,
its degree map and closed field subgroups, and the actual residue quotient
`D.residueQuotient K` of the multiplicative Type-zero profinite-integer model.
No replacement field, quotient or degree datum is introduced.

| Source unit | Source lines and name after `ClassFormation.DegreeData.` | Adapted data after the public prefix |
| --- | --- | --- |
| M010.021 | 165–171, `FiniteResidueAbstractField` | `FiniteResidueAbstractField` |
| M010.022 | 177–183, `FiniteResidueAbstractField.ofField` | `FiniteResidueAbstractField.ofField` |
| M010.023 | 185–188, `FiniteResidueAbstractField.toSubgroup` | `FiniteResidueAbstractField.toSubgroup` |
| M010.024 | 190–193, anonymous `Finite` instance | `Langlands.NYLL.PortInternal.M010.d024` (full name) |
| M010.025 | 195–198, `FiniteResidueAbstractField.residueDegree` | `FiniteResidueAbstractField.residueDegree` |

The source section supplies implicit `G : Type u`, `[Group G]` and
`[TopologicalSpace G]`. The structure has explicit `D : DegreeData G` and
contains exactly `field : ClosedSubgroup G` and
`finiteResidueQuotient : Finite (D.residueQuotient field)`.
Thus finite residue degree is a property of the actual quotient supplied
at this source boundary. It is not a finiteness assumption on the ambient
group or an extra field inserted into the earlier degree datum.

`ofField` retains explicit `D`, explicit `K : ClosedSubgroup G` and the
instance binder `[hfinite : Finite (D.residueQuotient K)]`, in that order.
It packages that field and its supplied finite-quotient instance.
For the remaining declarations, `D` is implicit and the bundled field
`K : FiniteResidueAbstractField D` is explicit. `toSubgroup` returns the
actual underlying subgroup `K.field.toSubgroup` and retains the source
`implicit_reducible` attribute. The named instance supplies the same stored
finiteness proof by projecting `K.finiteResidueQuotient`. It changes no
ambient group, ring or topology instance.

`residueDegree K : ℕ+` is the source positive natural number whose value is
`Nat.card (D.residueQuotient K.field)`. Its body constructs a local
`Nonempty` instance from the quotient class of the identity and applies
Mathlib's `Nat.card_pos`, using the stored finiteness instance above. The
quotient and its cardinal value are unchanged; positivity is derived by
this body, not supplied as a new field. No profiniteness,
`IsTopologicalGroup`, normality or additional topology hypothesis is added.
The arbitrary source universe `u` and binder kinds are preserved.

Worker 120 prefixes the source namespace, gives only the anonymous source
instance the stable inventory name, and replaces the original broad imports
with the focused published initial-data module. The source bodies,
structure fields, declaration kinds and retained attribute are unchanged.
The omitted source `open CyclicCohomology` is unused by these commands.
The source `noncomputable section` and explicit `noncomputable` degree
modifier remain. The original copyright and author header is retained.
Theorem commands M010.026–027 and all later extension, normalized-degree
and arithmetic-degree results are absent; no theorem proof or host
class-formation or reciprocity comparison is claimed.

The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
See the retained Apache-2.0 files `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
