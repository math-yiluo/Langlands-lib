# NYLL M080.001: restriction between named finite Galois quotients

The paired Lean file adapts the definition `bundledRestrictionHom` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean`.
The pinned source file has SHA-256
`c355b25591d40a48d3cf642a1015ae1f5b49d9a14df8a05516a2128c2b43856f`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.FiniteGaloisSubextension.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M080.001 | `bundledRestrictionHom` | 30 | 31–39 | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.bundledRestrictionHom` |

The enclosing source context is `noncomputable section` (line 18),
`namespace ClassFormation` (line 20), `open KummerTheory` (line 22),
`open CyclicCohomology` (line 23), the comment and variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (lines 25–26)
and `namespace FiniteGaloisSubextension` (lines 28–443). The only source
import is the unported module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction`
(line 7). The rest of the source file (lines 41–441, M080.002–M080.009) is not
part of this module; the statements of M080.008 and M080.009 are in the
sibling module `Reciprocity.TotallyRamifiedCase.RestrictionCosets.Statements`.

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001, from
  `GaloisCohomology.Cyclic.IntegralRepUniverse`), the abbreviation `Type 0`;
- `FiniteGaloisSubextension K` (M040.001, from
  `Reciprocity.FiniteGaloisSubextension.Definitions`), a finite Galois
  extension of the closed subgroup `K`, with fields `L.field` (the closed
  subgroup `G_L`), `L.below : L.field.toSubgroup ≤ K.toSubgroup`, the
  normality of `G_L` in `G_K` and the finiteness of `G_K ⧸ G_L`;
- `FiniteGaloisSubextension.extensionQuotient` (M040.004, same module), the
  type `G(L/K) = K.toSubgroup ⧸ extensionSubgroup K L.field L.below`, with
  its group instance (M040.008) and the normality instance
  `extensionSubgroup_normalInstance` (M040.007);
- `FiniteGaloisSubextension.extensionQuotientMulEquiv` (M040.010, same
  module), the identity multiplicative equivalence between
  `L.extensionQuotient` and the underlying Mathlib quotient;
- `abstractReciprocityRestriction` (M075.005, from
  `Reciprocity.Core.Restriction.Definitions`): for closed subgroups `K`, `M`,
  `L` with `hLM : L.toSubgroup ≤ M.toSubgroup`,
  `hMK : M.toSubgroup ≤ K.toSubgroup` and both `L` and `M` normal in `K`,
  the monoid homomorphism `G_K ⧸ G_L →* G_K ⧸ G_M` induced by the identity of
  `G_K` (the restriction `G(L/K) → G(M/K)`).

`ClosedSubgroup`, `MonoidHom.comp` and `MulEquiv.toMonoidHom` are Mathlib's.

## Definition

The definition has the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, followed by:

```lean
def bundledRestrictionHom
    {K : ClosedSubgroup G}
    (M L : FiniteGaloisSubextension K)
    (hML : M.field.toSubgroup ≤ L.field.toSubgroup) :
    M.extensionQuotient →* L.extensionQuotient :=
  L.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    ((abstractReciprocityRestriction
      K L.field M.field hML L.below).comp
        M.extensionQuotientMulEquiv.toMonoidHom)
```

For two finite Galois extensions `M` and `L` of `K` with `G_M ≤ G_L` (so the
field `M` contains the field `L`), the restriction homomorphism
`G(M/K) → G(L/K)`: the quotient map `G_K ⧸ G_M → G_K ⧸ G_L` induced by the
identity of `G_K`, read between the named quotient types through the two
identity equivalences. The normality instances of `abstractReciprocityRestriction`
are found from M040.007 for `M` and `L`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`
   (M040.001, M040.004, M040.007, M040.008, M040.010 and M004.002),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Definitions`
   (M075.005) and `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`
   (M002.001).
3. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition.
4. Omit the rest of the source file and the unused `open KummerTheory` and
   `open CyclicCohomology`. Retain the noncomputable section, the comment,
   the variable line and the namespaces.
5. The binders, docstring and body are unchanged.

No helper declaration or instance is added. This definition discharges
no host class-formation, cup, transfer, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
