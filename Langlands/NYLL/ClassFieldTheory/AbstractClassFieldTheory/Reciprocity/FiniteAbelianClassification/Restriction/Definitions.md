# NYLL M298.009: restriction between finite abelian subextensions

Worker 458, 14 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
(file SHA-256
`0bc99c03d0936ca803d6497174ef17999b76789381f183f525a9f098eac7fd83`), lines
235–246 (docstring 235–237, declaration 238–246), with the scaffolding at
lines 23–34. Registered source `external-lean-reuse-snapshots-2026-10-21`
(folder `n-yamaguchi-0729--ClassFieldTheory/source`), content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Name map

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M298.009 | `ClassFormation.FiniteAbelianSubextension.restriction` | 235–246 | `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.restriction` | def, `→*` |

This candidate also integrates the sibling pair
`FiniteAbelianClassification/QuotientInstances/Definitions.lean` and `.md`,
which port the source local instances M298.001 and M298.002 as
`Langlands.NYLL.PortInternal.M298.d001` and
`Langlands.NYLL.PortInternal.M298.d002`. That pair's own Markdown documents
those two instances. They are in this candidate because they are
proposition-valued, so Lean records them as theorems, and a definition record
needs a definition as its declaration.

## The definition

**`restriction`** (M298.009). Telescope, exactly as in the source: implicit
`{G : Type*}` (a universe-polymorphic type, the single universe parameter
`u_1`), instance arguments `[Group G] [TopologicalSpace G]`, implicit
`{K : ClosedSubgroup G}`, implicit `{L₁ L₂ : FiniteAbelianSubextension K}` and
explicit `(h₁₂ : L₁ ≤ L₂)`. No `IsTopologicalGroup G` or class-formation
hypothesis is added.

`L₁ ≤ L₂` is the order on finite abelian subextensions, M296.014
(`Langlands.NYLL.PortInternal.M296.d014`, source `FiniteAbelianSubextension.lean`
lines 144–155). It is field inclusion `L₁ ⊆ L₂`, which is the reverse
inclusion of absolute Galois subgroups: by definition
`L₁ ≤ L₂` is `L₂.field.toSubgroup ≤ L₁.field.toSubgroup`.

The result has type `L₂.extensionQuotient →* L₁.extensionQuotient`, a monoid
homomorphism between the actual named Galois quotients `G(L₂/K)` and
`G(L₁/K)` of the published M296 boundary, with their published `CommGroup`
structures. The body is the source body:

```lean
  letI : (extensionSubgroup K L₁.field L₁.below).Normal := L₁.normal
  letI : (extensionSubgroup K L₂.field L₂.below).Normal := L₂.normal
  exact L₁.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    ((abstractReciprocityRestriction K L₁.field L₂.field h₁₂ L₁.below).comp
      L₂.extensionQuotientMulEquiv.toMonoidHom)
```

So `restriction h₁₂` is the composite

`L₂.extensionQuotient ≃* K/G_{L₂} → K/G_{L₁} ≃* L₁.extensionQuotient`,

whose middle map is the actual
`Langlands.NYLL.ClassFormation.abstractReciprocityRestriction K L₁.field L₂.field h₁₂ L₁.below`
(M075.005): the map of raw quotients `G_K / G_{L₂} → G_K / G_{L₁}` induced by
the identity of `G_K`, which is well defined because `G_{L₂} ≤ G_{L₁}` (here
`h₁₂` is used exactly as the inclusion `hLM`). The two outer maps are the
published boundary equivalences `extensionQuotientMulEquiv` of `L₂` and the
inverse of that of `L₁` (M296.009). The two `letI` normality proofs supply the
instance arguments of `abstractReciprocityRestriction`.

## Reused Library declarations

- `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` (M296.001) with
  `field`, `below`, `normal` (M296.002–.004), `extensionQuotient` (M296.006),
  its `CommGroup` instance (M296.007) and `extensionQuotientMulEquiv`
  (M296.009), from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`.
- The order instance `Langlands.NYLL.PortInternal.M296.d014` (M296.014), from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Order`.
- `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction` (M075.005),
  from `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Definitions`.
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
  abbreviation for `L.toSubgroup.subgroupOf K.toSubgroup`, reached by name
  through `open CyclicCohomology`, as in the source.
- `Langlands.NYLL.PortInternal.M298.d001` and `d002`, from the integrated
  sibling module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification.QuotientInstances.Definitions`.

## Instance scope

In the source, the two local instances M298.001 and M298.002 (lines 36–46)
are in force from their declaration to `end FiniteAbelianSubextension` at
line 516, so they are in scope at M298.009. The adaptation reproduces this:
inside `namespace FiniteAbelianSubextension` the module runs

```lean
attribute [local instance] Langlands.NYLL.PortInternal.M298.d001
  Langlands.NYLL.PortInternal.M298.d002
```

before the definition. The attribute is local to that namespace and is not
exported, so no global instance is added. A private `#print` of the
elaborated definition shows that the two instance arguments of
`abstractReciprocityRestriction` are `L₂.normal` and `L₁.normal`, the values
of the two `letI`s in the body, as in the source.

## Source scaffolding

Lines 23–34 of the source are `noncomputable section`,
`namespace ClassFormation`, `open CyclicCohomology KummerTheory`, the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 30),
`namespace FiniteAbelianSubextension` and `variable {K : ClosedSubgroup G}`
(line 34). The definition binds its own `{G : Type*}`, `[Group G]`,
`[TopologicalSpace G]` and `{K : ClosedSubgroup G}`, which shadow the section
variables, so the section variables do not enter its telescope in the source.

## Modifications

Worker 458 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
2. The section variables of source lines 30 and 34 are omitted: they are
   shadowed by the definition's own binders and enter no telescope.
   `open KummerTheory` is omitted because the definition does not use it;
   `open CyclicCohomology` is kept.
3. The two source local instances are declared in the sibling module
   `QuotientInstances/Definitions` (as local instances there) and installed
   here with `attribute [local instance]`, as described above.
4. The source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldCandidate`
   and `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main` are
   replaced by the published imports the definition uses: the
   `QuotientInstances` sibling module, the M296.014 order module and the
   `abstractReciprocityRestriction` module.
5. The module gets a module docstring and a modification notice.

The docstring, universes, binders, binder kinds, result type and body are
otherwise unchanged. A focused `lean_check` of this module reports no errors
or warnings.

## Source declarations not in this module

The target M298.010 (`restriction_mk`) and the target M298.017
(`eq_of_le_of_extensionQuotient_card_eq`) are stated in the sibling module
`FiniteAbelianClassification/Restriction/Statements`. The compositum
restriction helpers M298.011–.016 and the remaining declarations of the
source file are ported elsewhere.

## Scope

This is a data definition only. No reciprocity, class-formation or
cohomological statement is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
