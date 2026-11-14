# NYLL M295.001: the norm subgroup of a finite Galois subextension

This is the namespaced adaptation of Naganori Yamaguchi's
`ClassFormation.FiniteGaloisSubextension.normSubgroup`, source unit M295.001,
from `n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The exact source is
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/NormTopology.lean`,
lines 39–43, with its declaration docstring at lines 37–38 and surrounding
parameter declarations at lines 31 and 35. The source file has SHA-256
`a9f6f1181acee92e8121cabaa565de120576530c2955bb3cc37665f464a0e40b`.
The readable pinned source is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Source name | Adapted name | Role |
| --- | --- | --- |
| `ClassFormation.FiniteGaloisSubextension.normSubgroup` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.normSubgroup` | The definition in this file, M295.001 |
| `ClassFormation.FiniteGaloisSubextension` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension` | Reused M040.001 structure and its generated projections `field`, `below`, `finite` |
| `ClassFormation.finiteNormSubgroup` | `Langlands.NYLL.ClassFormation.finiteNormSubgroup` | Reused actual finite norm subgroup, M039.001 |
| `KummerTheory.ambientFixedAddSubgroup` | `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` | Reused fixed additive subgroup, M023.001 |
| `IntegralRepGroupType` | `Langlands.NYLL.IntegralRepGroupType` | Reused universe-zero boundary, M002.001 |

Mathlib's `Rep`, `ClosedSubgroup`, and `AddSubgroup` retain their names.

## Telescope and construction

The complete telescope, in order, is implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, instance `[Group G]`, instance
`[TopologicalSpace G]`, implicit `{K : ClosedSubgroup G}`, explicit
`(A : Rep ℤ G)`, and explicit
`(L : Langlands.NYLL.ClassFormation.FiniteGaloisSubextension K)`.
The published abbreviation `IntegralRepGroupType := Type 0` retains the
source's universe-zero acting-group boundary.
The result is the actual
`AddSubgroup (Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup A K)`.

The body is unchanged:

```lean
by
  letI := L.finite
  exact finiteNormSubgroup A K L.field L.below
```

The local instance is the bundle's finiteness witness for
`K.toSubgroup ⧸ extensionSubgroup K L.field L.below`.
Published M039.001 writes the same quotient using the definitionally equal
`L.field.toSubgroup.subgroupOf K.toSubgroup`; the source abbreviation
`extensionSubgroup` has exactly this body, so no conversion is needed.
M039.001 is the range of the actual additive relative norm from the
fixed subgroup for `L.field` to the fixed subgroup for `K`.
This definition passes `L.field` and the inclusion witness `L.below`
directly to that construction. The argument is the finite Galois bundle,
with its source normality and finiteness fields.
There is no compactness, topological-group or abelian-extension hypothesis.
The only instance installed by this file is `L.finite` inside the body.

## Imports and modifications

Worker 507 made the following changes:

1. Extract only M295.001, its docstring and the required source scaffolding.
   Preserve `noncomputable section`, both namespace scopes, the
   `open CyclicCohomology KummerTheory` command, both parameter declarations
   and the complete definition body.
2. Prefix the source `ClassFormation` namespace with `Langlands.NYLL`.
   References to existing NYLL support resolve to the names in the table.
3. Replace the source imports by:

   - `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`,
     supplying the published M040 bundle and projections.
   - `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`,
     supplying M039.001 and its fixed-subgroup/relative-norm dependencies.
   - `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`,
     supplying the source universe boundary.

   The source imports of
   `Mathlib.Algebra.Group.TransferInstance`,
   `Mathlib.Topology.Algebra.FilterBasis`, and
   `Nyll.ValuedFieldTheory.Valuation.Topology.Models`
   support later declarations and are omitted.
   `Mathlib.Topology.Algebra.Group.ClosedSubgroup` is available through the
   focused support imports. The source
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension`
   import is split into the M040 data import and the explicit M039
   construction import because published M040 data no longer imports M039.
   The source integral-representation import is replaced by its namespaced
   Library counterpart.
4. Replace the original module docstring about the full norm topology by a
   focused module docstring recording the extraction and modifications.
   Close the extracted namespace and section scopes at the end of the file.

No telescope, construction body, binder kind or declaration attribute changes.
No theorem target or further M295 declaration is included.

## Attribution

The original copyright and author header is retained verbatim.
The Library carries the Apache-2.0 license at `licenses/NYLL/LICENSE`
(SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and the upstream notice at `licenses/NYLL/NOTICE`
(SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This definition supplies the packaged finite Galois norm subgroup interface.
