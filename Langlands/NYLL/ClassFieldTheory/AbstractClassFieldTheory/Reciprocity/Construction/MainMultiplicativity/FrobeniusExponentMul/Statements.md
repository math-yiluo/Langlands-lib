# NYLL M053.001: the Frobenius exponent is additive

The paired Lean file adapts the statement of the theorem `DegreeData.frobeniusExponent_mul` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean`.
The pinned source file has SHA-256
`913562295296948d960ad31a3f03b201046ba2089b481705109cd238619c3445`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Attribute | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- | --- |
| M053.001 | `frobeniusExponent_mul` | 37–38 | 39 (`@[simp]`) | 40–47 | 47–67 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusExponent_mulStatement` |

The enclosing source context is `universe u` (line 20),
`namespace ClassFormation` (line 22), `open KummerTheory` (line 24),
`open CyclicCohomology` (line 25), `noncomputable section` (line 27),
`open CategoryTheory` (line 29), `section frobeniusAlgebra` (lines 31–71),
the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 33) and
`namespace DegreeData` (lines 35–69). The source imports (lines 7–9) are the
unported modules `FrobeniusDescent`, `Universal` and `TransferOrbitClosure`
of `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction`.
The rest of the source file is not part of this module; M053.003 and the
target of M053.004 are published in
`Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder`.

The names used resolve to `Langlands.NYLL` declarations:

- `DegreeData` (M010.002) and `DegreeData.FiniteResidueAbstractField D`
  (M010.021), a closed subgroup `K.field` whose residue quotient is finite;
- `CyclicCohomology.extensionSubgroup` (M004.002, from
  `GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`), the
  abbreviation `extensionSubgroup K L hLK = L.toSubgroup.subgroupOf K.toSubgroup`;
- `DegreeData.FrobeniusElements` (M012.009, from
  `Degree.FrobeniusLift.FrobeniusElements.Definitions`), the subtype of
  elements `σ` of `G_K ⧸ (G_L ⊓ I_K)` whose normalized degree is
  `(Multiplicative.ofAdd 1) ^ n` for some natural `n > 0`;
- `DegreeData.frobeniusExponent` (M014.012, from
  `Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`), the chosen such
  `n` of a Frobenius element;
- the instance `DegreeData.frobeniusElementsMul` (M015.002, from
  `Reciprocity.Construction.FrobeniusSemigroup.Definitions`), the
  multiplication `σ₁ * σ₂ = D.frobeniusMul K L hLK σ₁ σ₂` (M015.001, same
  module), the Frobenius element with underlying quotient element
  `σ₁.1 * σ₂.1`.

## Target and complete telescope

The target has the binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, followed by:

```lean
def frobeniusExponent_mulStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ₁ σ₂ : D.FrobeniusElements K L hLK) : Prop :=
    D.frobeniusExponent K L hLK (σ₁ * σ₂) =
      D.frobeniusExponent K L hLK σ₁ +
      D.frobeniusExponent K L hLK σ₂
```

The Frobenius exponent of a product of two Frobenius elements is the sum of
their exponents.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `@[simp] theorem frobeniusExponent_mul … : statement := proof` by
   `def frobeniusExponent_mulStatement … : Prop := statement`. The telescope
   and statement are copied verbatim. The `@[simp]` attribute is omitted: a
   definition of a proposition is not a rewriting lemma, and the attribute
   belongs on the eventual proof. The source proof is omitted: this
   contribution publishes the proposition target, and its proof is separate
   work.
3. Prefix the source docstring with `Target:`, lower-case the first word
   after it and rewrap the lines; the wording is unchanged. Replace the
   source module docstring by a description of this module with a
   modification notice that names the source theorem.
4. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup.Definitions`
   (M015.001 and M015.002, which also bring M010.002, M010.021, M012.009 and
   M014.012) and
   `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
   (M004.002).
5. Omit the other declarations of the source file and the unused
   `open KummerTheory` and `open CategoryTheory`. Retain the universe,
   `open CyclicCohomology` (for `extensionSubgroup`), the noncomputable
   section, the section `frobeniusAlgebra`, the variable line and the
   namespaces. Every binder occurs in the proposition or is used by
   `FrobeniusElements`, so no linter option is needed.
6. No helper declaration or instance is added.

This is an exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate
or reciprocity target.

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
