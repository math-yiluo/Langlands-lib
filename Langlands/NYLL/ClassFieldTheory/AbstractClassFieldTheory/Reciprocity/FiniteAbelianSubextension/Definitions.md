# NYLL M296: finite abelian subextension data

Worker 159, 13 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
(file SHA-256 `f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`),
lines 30–52 (scaffolding) and 42–108 (the ten units below). Registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).

## Name map

Adapted names carry the prefix `Langlands.NYLL.ClassFormation.`, original names
the prefix `ClassFormation.`; `FAS` abbreviates `FiniteAbelianSubextension` in
both columns. Line ranges include the docstring and attributes.

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M296.001 | `FAS` | 42–48 | `FAS` | structure |
| M296.002 | `FAS.field` | 54–56 | `FAS.field` | abbrev |
| M296.003 | `FAS.below` | 58–61 | `FAS.below` | abbrev |
| M296.004 | `FAS.normal` | 63–66 | `FAS.normal` | abbrev |
| M296.005 | `FAS.finite` | 68–71 | `FAS.finite` | abbrev |
| M296.006 | `FAS.extensionQuotient` | 73–78 | `FAS.extensionQuotient` | def, `Type u` |
| M296.007 | `FAS.extensionQuotient_commGroup` | 80–90 | `FAS.extensionQuotient_commGroup` | instance |
| M296.008 | `FAS.extensionQuotient_finite` | 92–96 | `FAS.extensionQuotient_finite` | instance |
| M296.009 | `FAS.extensionQuotientMulEquiv` | 98–103 | `FAS.extensionQuotientMulEquiv` | def, `≃*` |
| M296.010 | `FAS.extensionQuotientMk` | 105–108 | `FAS.extensionQuotientMk` | def, `→*` |

The source theorems M296.011–.013 (lines 110–142) are stated as Prop-valued
targets in the sibling module `FiniteAbelianSubextension/Statements`.

## Telescope and objects

The source scaffolding is kept: `noncomputable section` (line 30),
`namespace ClassFormation` (32), `open CyclicCohomology` (34, see
modification 3), `universe u` (36), `section GroupOnly` (38) with
`variable {G : Type u} [Group G] [TopologicalSpace G]` (40), and
`namespace FiniteAbelianSubextension` (50) with
`variable {K : ClosedSubgroup G}` (52). No `IsTopologicalGroup G` assumption and
no universe restriction is added.

- **M296.001.** `FiniteAbelianSubextension (K : ClosedSubgroup G)`, with
  implicit `{G : Type u}`, `[Group G]`, `[TopologicalSpace G]`, has exactly the
  two source fields, in source order:
  `toFiniteGaloisExtension : FiniteGaloisSubextension K` (the published M040
  finite Galois subextension: a closed subgroup `G_L ≤ G_K` whose relative
  subgroup is normal with finite quotient) and
  `commutative : IsMulCommutative toFiniteGaloisExtension.extensionQuotient`,
  Mathlib's commutativity predicate for the actual named quotient
  `G_K / G_L` with its published group structure.
- Every namespace declaration has implicit `{G : Type u}`, `[Group G]`,
  `[TopologicalSpace G]`, implicit `{K : ClosedSubgroup G}` and explicit
  `(L : FiniteAbelianSubextension K)`.
- **M296.002–.005** are the source abbreviations (reducible definitions)
  forwarding the four fields of `L.toFiniteGaloisExtension`:
  `field : ClosedSubgroup G`; `below : L.field.toSubgroup ≤ K.toSubgroup`;
  `normal : (extensionSubgroup K L.field L.below).Normal`;
  `finite : Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)`.
  The last three have proposition-valued types, as in the source.
- **M296.006.** `extensionQuotient L : Type u` is the def
  `L.toFiniteGaloisExtension.extensionQuotient`, with the source attribute
  `@[implicit_reducible]`. It is therefore the named M040 boundary, whose body
  is `K.toSubgroup ⧸ extensionSubgroup K L.field L.below`; no transparent
  quotient abbreviation is introduced. The result stays in `Type u`.
- **M296.007.** Global instance `extensionQuotient_commGroup L :
  CommGroup L.extensionQuotient`, with `@[implicit_reducible]`: after unfolding
  `extensionQuotient`, it extends the published group instance
  (`FiniteGaloisSubextension.extensionQuotient_groupInstance`) by
  `mul_comm := L.commutative.is_comm.comm`. Its multiplication is therefore
  that of the actual quotient group.
- **M296.008.** Global instance `extensionQuotient_finite L :
  Finite L.extensionQuotient`, obtained after unfolding from the published
  `FiniteGaloisSubextension.extensionQuotient_finiteInstance`.
- **M296.009.** `extensionQuotientMulEquiv L : L.extensionQuotient ≃*
  (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)` is
  `L.toFiniteGaloisExtension.extensionQuotientMulEquiv` (which is
  `MulEquiv.refl _`).
- **M296.010.** `extensionQuotientMk L : K.toSubgroup →* L.extensionQuotient`
  is `L.toFiniteGaloisExtension.extensionQuotientMk`, i.e. the quotient map
  `QuotientGroup.mk'`.

The two instances are global in the source and remain global; they are the
only instances added, and they live on the new named type
`FiniteAbelianSubextension.extensionQuotient`. A private check confirmed that
the group underlying the new `CommGroup` instance agrees by `rfl` (at default
transparency; not at reducible-and-instances transparency) with the published
finite Galois quotient group `extensionQuotient_groupInstance`.

## Reused Library declarations

- `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension` (M040.001) and its
  `extensionQuotient` (M040.004), `extensionQuotient_groupInstance` (M040.008),
  `extensionQuotient_finiteInstance` (M040.009), `extensionSubgroup_normalInstance`
  (M040.007), `extensionQuotientMulEquiv` (M040.010) and `extensionQuotientMk`
  (M040.011), all from the published module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`.
  This is the source's own boundary (`toFiniteGaloisExtension` field); it is not
  duplicated.
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), used under its
  own name through `open CyclicCohomology`, so the source spelling
  `extensionSubgroup K L.field L.below` is kept.
- Mathlib's `ClosedSubgroup`, `IsMulCommutative`, `CommGroup`, `Finite`,
  `QuotientGroup`, `MulEquiv` and `MonoidHom`.

## Modifications

Worker 159 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
2. The source imports
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension`,
   `Mathlib.Algebra.Group.Subgroup.Pointwise` and
   `Mathlib.Topology.Algebra.Group.Pointwise` are replaced by the single published
   module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`.
   The pointwise imports serve later source declarations (normalizer and
   intersection, from line 273) that are not part of this unit; a clean focused
   check confirms they are unnecessary here.
3. `open CyclicCohomology KummerTheory` (line 34) becomes `open CyclicCohomology`:
   none of these declarations uses a `KummerTheory` name, and that namespace is
   not imported by the focused import.
4. The source module docstring (lines 11–26) is replaced by a short docstring
   recording these modifications.
5. Only lines 42–108 are ported. The theorems at lines 110–142 are stated in the
   sibling `Statements` module; source declarations from line 144 on (order,
   base change, compositum, intersection, norm subgroup and the
   `Representation` section) belong to other tasks and are omitted. The
   commands `end FiniteAbelianSubextension` and `end GroupOnly` (source lines
   400 and 402) close the shortened sections; as in the source, the
   `noncomputable section` is left open to the end of the file.

Declarations, binders, attributes, docstrings and bodies are otherwise
unchanged.

## Validation

The module compiles in the project Lean service (environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings. A private
check also verified `L.extensionQuotient = (K.toSubgroup ⧸ extensionSubgroup K
L.field L.below)` by `rfl`, commutativity and finiteness by instance search,
and that the source proofs of M296.011–.013 inhabit the sibling targets. These
checks establish compilation and source correspondence only; independent review
is still required. This support unit makes no class-formation or reciprocity
assertion.
