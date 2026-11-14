# NYLL M298.001–.002: local quotient instances of a finite abelian subextension

Worker 458, 14 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
(file SHA-256
`0bc99c03d0936ca803d6497174ef17999b76789381f183f525a9f098eac7fd83`), lines
36–40 and 42–46, with the scaffolding at lines 23–34. Registered source
`external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`), content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Name map

Original names have the prefix `ClassFormation.FiniteAbelianSubextension.`.
Neither source instance has a docstring or attribute other than `local
instance`.

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M298.001 | `extensionQuotient_normal` | 36–40 | `Langlands.NYLL.PortInternal.M298.d001` | local instance, Prop-valued |
| M298.002 | `representedQuotient_finite` | 42–46 | `Langlands.NYLL.PortInternal.M298.d002` | local instance, Prop-valued |

The adapted names are the reserved `PortInternal` names of the NYLL port
inventory (`notes/reuse/nyll-public-port/m289-m312.md`, section M298).

## The declarations

Both instances have the source's own telescope: implicit `{G : Type*}`
(a universe-polymorphic type, the single universe parameter `u_1`),
instance arguments `[Group G] [TopologicalSpace G]`, implicit
`{K : ClosedSubgroup G}`, and explicit `(L : FiniteAbelianSubextension K)`.
No `IsTopologicalGroup G` or class-formation hypothesis is added.

- **`d001`** (M298.001) has type
  `(extensionSubgroup K L.field L.below).Normal` and body `L.normal`: the
  subgroup `G_L ∩ G_K`, viewed inside `G_K`, is normal.
- **`d002`** (M298.002) has type
  `Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)` and body
  `L.finite`: the raw quotient `G_K / G_L` is finite.

Both are proposition-valued, so Lean records them as theorems carrying the
instance attribute, as in the source. They repeat two field projections of
the published structure:

- `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` (M296.001) and its
  abbreviations `field`, `below`, `normal` and `finite` (M296.002–.005), from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`;
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
  abbreviation for `L.toSubgroup.subgroupOf K.toSubgroup`, reached by name
  through `open CyclicCohomology`, as in the source.

## Instance scope

In the source both are `local instance`s declared inside
`namespace FiniteAbelianSubextension` (opened at line 32), so the instance
attribute is in force only until `end FiniteAbelianSubextension` at source
line 516, and it is not exported to importing files. The adaptation keeps
this exactly: both are `local instance`s declared with `_root_.` inside
`namespace FiniteAbelianSubextension` of the paired Lean file, so after an
import they are ordinary named theorems, not instances. Neither becomes a
global instance, so they cannot conflict with Mathlib or Library instances.

The source declarations that used the instances are lines 48–515 of the same
namespace. An adapted consumer that needs the same scope installs them
locally, with

```lean
attribute [local instance] Langlands.NYLL.PortInternal.M298.d001
  Langlands.NYLL.PortInternal.M298.d002
```

in the corresponding section or namespace.

A private check (not part of this candidate) importing the module found:

- `Lean.Meta.isInstance` reports `false` for both names.
- Without the `attribute [local instance]` line, instance search finds
  `(extensionSubgroup K L.field L.below).Normal` only through the published
  global instance
  `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance`
  (M040.007) applied to `L.toFiniteGaloisExtension`. It does not find
  `Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)`.
- With that line, `#synth` returns `Langlands.NYLL.PortInternal.M298.d001 L`
  and `Langlands.NYLL.PortInternal.M298.d002 L` for these two propositions.

## Source scaffolding

Lines 23–34 of the source are `noncomputable section`,
`namespace ClassFormation`, `open CyclicCohomology KummerTheory`, the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 30),
`namespace FiniteAbelianSubextension` and `variable {K : ClosedSubgroup G}`
(line 34). Both instances bind their own `{G : Type*}`, `[Group G]`,
`[TopologicalSpace G]` and `{K : ClosedSubgroup G}`, which shadow the section
variables; the section variables therefore do not enter either telescope in
the source.

## Modifications

Worker 458 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
2. The source names `extensionQuotient_normal` and `representedQuotient_finite`
   become the reserved names `Langlands.NYLL.PortInternal.M298.d001` and
   `Langlands.NYLL.PortInternal.M298.d002`, written with `_root_.` inside
   `namespace FiniteAbelianSubextension` so that the local scope is the same
   namespace as in the source.
3. The section variables of source lines 30 and 34 are omitted: they are
   shadowed by the instances' own binders and enter no telescope (see above).
   `open KummerTheory` is omitted because neither declaration uses it;
   `open CyclicCohomology` is kept.
4. The source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldCandidate`
   and `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main` are
   replaced by the single published import these declarations use,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`.
5. Each instance gets a docstring naming its source name; the module gets a
   module docstring and a modification notice.
6. The other declarations of the source file are not in this module (see
   below).

Universes, binders, binder kinds, the `local instance` scope, types and bodies
are otherwise unchanged. A focused `lean_check` of this module reports no
errors or warnings.

## Source declarations not in this module

The rest of `FiniteAbelianClassification.lean` (M298.003–.036) is ported in
other modules of the same directory. The restriction homomorphism M298.009 is
in the sibling module `FiniteAbelianClassification/Restriction/Definitions`,
and the targets M298.010 and M298.017 are in
`FiniteAbelianClassification/Restriction/Statements`; both install these two
instances locally, as described above.

## Scope

These are two instance wrappers for structure fields. No reciprocity,
class-formation or cohomological statement is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
