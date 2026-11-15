# NYLL M074.010–M074.014: the order of a cyclic norm quotient under the class-field axiom

The paired Lean file adapts the statements of the theorems `finiteNormQuotientFiniteOfClassFieldAxiom`, `finiteNormQuotient_card_of_classFieldAxiom`, `additiveExtensionQuotient_card`, `cyclicReciprocity_card_equality` and `finiteNormQuotient_finite_of_classFieldAxiom` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`.
The pinned source file has SHA-256
`6dc5f10e7546a7b85d7712388b443344fe87679ef13d0eadb0f3451f925c731a`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M074.010 | `finiteNormQuotientFiniteOfClassFieldAxiom` | 377–378 | 379–388 | 388–407 | `Langlands.NYLL.ClassFormation.finiteNormQuotientFiniteOfClassFieldAxiomStatement` |
| M074.011 | `finiteNormQuotient_card_of_classFieldAxiom` | 409–410 | 411–421 | 421–455 | `Langlands.NYLL.ClassFormation.finiteNormQuotient_card_of_classFieldAxiomStatement` |
| M074.012 | `additiveExtensionQuotient_card` | 457 | 458–464 | 464–483 | `Langlands.NYLL.ClassFormation.additiveExtensionQuotient_cardStatement` |
| M074.013 | `cyclicReciprocity_card_equality` | 485–486 | 487–500 | 500–503 | `Langlands.NYLL.ClassFormation.cyclicReciprocity_card_equalityStatement` |
| M074.014 | `finiteNormQuotient_finite_of_classFieldAxiom` | 505 | 506–515 | 515–516 | `Langlands.NYLL.ClassFormation.finiteNormQuotient_finite_of_classFieldAxiomStatement` |

The enclosing source context is `namespace ClassFormation` (lines 21–519),
`open KummerTheory` (line 23), `open CyclicCohomology` (line 25),
`noncomputable section` (lines 29–518), `open CategoryTheory` (line 31) and
the comment and variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (lines 33–34).
The source imports (lines 7–9) are the modules `Construction.FiniteNormQuotient`,
`ClassFieldAxiom` and `FieldRepresentation` of
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity`. The rest of
the source file (lines 36–375, M074.001–M074.009) is not part of this
module.

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001, from
  `GaloisCohomology.Cyclic.IntegralRepUniverse`), the abbreviation `Type 0`;
- `SatisfiesClassFieldAxiom A` (M072.002, from
  `Reciprocity.ClassFieldAxiom.Definitions`): for every
  `K : FiniteAbstractField G` and every finite cyclic extension
  `E : FiniteCyclicSubextension K`, the class-field-axiom data M072.001,
  that is, the degree-zero and degree-minus-one Tate cohomology groups of
  `G(L/K)` with coefficients in `A_L` are finite, of orders `[L : K]` and `1`;
- `DegreeData.FiniteAbstractExtension G` (M010.065, from
  `Degree.Fields.FiniteExtension.Definitions`), closed subgroups `E.field`
  and `E.base` with `E.below : E.field.toSubgroup ≤ E.base.toSubgroup` and
  the finiteness `E.finiteQuotient` of `E.base.toSubgroup ⧸
  E.field.toSubgroup.subgroupOf E.base.toSubgroup`, also exported as the
  instance `representedQuotientFinite` (M010.078, same module);
- `DegreeData.FiniteAbstractExtension.degree` (M010.085, same module), the
  positive natural `Nat.card` of that coset space, the degree `[E.field : E.base]`;
- `baseField G` (M010.003, from `Degree.Fields.Definitions`), the closed
  subgroup `⊤` representing the distinguished base field, and
  `le_baseField K` (M010.005, from `Degree.Fields.U005.Proofs`), the proof
  that `K.toSubgroup ≤ (baseField G).toSubgroup`;
- `CyclicCohomology.extensionSubgroup` (M004.002, from
  `GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`), the
  abbreviation `extensionSubgroup K L hLK = L.toSubgroup.subgroupOf K.toSubgroup`;
- `FiniteNormQuotient A K L hLK` (M039.002, from
  `Reciprocity.Construction.FiniteNormQuotient.Definitions`), the quotient
  `A^{G_K} ⧸ N_{L|K} A^{G_L}` of the fixed group of `G_K` by the image of
  the relative norm, with the instance argument
  `Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)`, found here
  from M010.078.

`Rep ℤ G`, `ClosedSubgroup`, `Subgroup.Normal`, `Subgroup.zpowers`,
`Additive`, `Finite` and `Nat.card` are Mathlib's.

## Targets and complete telescopes

All five targets have the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, followed by those shown. Write
`G_K = E.base`, `G_L = E.field` and `G(L/K)` for the coset space
`G_K ⧸ G_L` (the subgroup `G_L` of `G_K`).

### M074.010

```lean
def finiteNormQuotientFiniteOfClassFieldAxiomStatement
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    Finite (FiniteNormQuotient A E.base E.field E.below)
```

Let `A` satisfy the class-field axiom and let `E` be a finite extension
`L | K` with `K` finite over the base field (`hKfinite`), `G_L` normal in
`G_K` and `G(L/K)` generated by `g` (so cyclic). Then the norm quotient
`A^{G_K} ⧸ N_{L|K} A^{G_L}` is finite.

### M074.011

```lean
def finiteNormQuotient_card_of_classFieldAxiomStatement
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    Nat.card (FiniteNormQuotient A E.base E.field E.below) =
      (E.degree : ℕ)
```

Under the same hypotheses, the norm quotient has exactly `[L : K]` elements.

### M074.012

```lean
def additiveExtensionQuotient_cardStatement
    (E : DegreeData.FiniteAbstractExtension G) : Prop :=
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
      (E.degree : ℕ)
```

For every finite abstract extension, the additive copy of `G(L/K)` has
`[L : K]` elements. No cyclicity or class-field hypothesis is involved.

### M074.013

```lean
def cyclicReciprocity_card_equalityStatement
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
      Nat.card (FiniteNormQuotient A E.base E.field E.below)
```

Under the hypotheses of M074.010 (the finiteness of `K` over the base is an
anonymous instance argument), the additive copy of `G(L/K)` and the norm
quotient have the same number of elements.

### M074.014

```lean
def finiteNormQuotient_finite_of_classFieldAxiomStatement
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    Finite (FiniteNormQuotient A E.base E.field E.below)
```

The proposition of M074.010 again, with the finiteness of `K` over the base
as an anonymous instance argument; the source proves it by applying
M074.010.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. Each telescope and statement
   is copied verbatim. The source proofs are omitted: this contribution
   publishes the proposition targets, and their proofs are separate work.
3. Prefix each source docstring with `Target:`, lower-case the first word
   after it and rewrap the lines; the wording is unchanged. Replace the
   source module docstring by a description of
   this module with a modification notice that names the source theorems.
4. Put `set_option linter.unusedVariables false in` before the four targets
   with class-field hypotheses. Their propositions do not mention the
   binders `hcf`, `hnormal` and `hg` (and, for M074.010 and M074.011, the
   named instance binder `hKfinite`), and the linter would otherwise warn;
   the option changes no declaration. M074.012 has no such binder.
5. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`
   (M039.002),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Definitions`
   (M072.002, which also brings M002.001, M010.065, M010.078 and M010.085),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`
   (M010.005, which also brings M010.003) and
   `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
   (M004.002).
6. Omit the other declarations of the source file and the unused
   `open KummerTheory` and `open CategoryTheory`. Retain
   `open CyclicCohomology` (for `extensionSubgroup`), the noncomputable
   section, the comment, the variable line and the namespace.
7. No helper declaration or instance is added.

These are exact source statements as named propositions, without
published proofs. They discharge no host class-formation, cup, transfer,
Tate or reciprocity target.

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
