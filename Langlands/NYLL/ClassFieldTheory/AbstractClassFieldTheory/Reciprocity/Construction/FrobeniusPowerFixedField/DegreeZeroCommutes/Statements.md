# NYLL M038.001–M038.003: degree-zero commutation and degrees of Frobenius powers

The paired Lean file adapts the statements of three theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`.
The pinned source file has SHA-256
`4f9719760da9ac7344ece27b3aaf46d4acbd1d1295202dbb9eb84b41bc9b4256`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M038.001 | `extensionInertia_commutes_of_mem_extensionSubgroup` | 37–41 | 42–51 | 51–71 | `Langlands.NYLL.ClassFormation.DegreeData.extensionInertia_commutes_of_mem_extensionSubgroupStatement` |
| M038.002 | `quotientPower_card_commutes_degreeZero` | 73–77 | 78–89 | 89–126 | `Langlands.NYLL.ClassFormation.DegreeData.quotientPower_card_commutes_degreeZeroStatement` |
| M038.003 | private `extensionNormalizedDegree_pow_of_degreeOne` | none | 128–136 | 136–138 | `Langlands.NYLL.PortInternal.M038.d003Statement` |

The source context is `universe u` (line 17), `namespace ClassFormation`
(line 19), `open KummerTheory` (line 21), `open CyclicCohomology` (line
22), `noncomputable section` (line 26), `open CategoryTheory` (line 28),
`open scoped BigOperators` (line 29), `section degreeOnePowerFields` (line
31), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 33)
and `namespace DegreeData` (line 35). The source import is the NYLL module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum`
(line 7). The other declarations of the source file are outside this
contribution.

The statements use these published declarations:

- `DegreeData G` (M010.002, from `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`), the
  degree datum: a continuous homomorphism `degree : G →ₜ* ZHatMul`, where
  `ZHatMul` is `Multiplicative ZHat`, with `degree_surjective`;
- `DegreeData.FiniteResidueAbstractField D` (M010.021, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions`), an abstract field
  `K.field : ClosedSubgroup G` with finite residue degree;
- `D.extensionInertiaWithin K.field L hLK` (M012.002, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions`), the subgroup
  `L.toSubgroup.subgroupOf K.toSubgroup ⊓ D.fieldInertiaWithin K` of
  `G_K`, the inertia subgroup of `L` inside `G_K`, normal under the
  hypothesis `hLnormal` by the instance M012.003, so that the quotient
  `G(\widetilde L/K) = G_K ⧸ I_L` is a group;
- `D.extensionNormalizedDegree K L hLK` (M012.005, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions`), the homomorphism
  `G_K ⧸ I_L →* ZHatMul` induced by the normalized degree `d_K = (1/f_K) d`
  (M011.006); elements with value `1` are the degree-zero elements;
- `D.FrobeniusElements K L hLK` (M012.009, same module), the subtype of
  `σ : G_K ⧸ I_L` with `D.extensionNormalizedDegree K L hLK σ =
  (Multiplicative.ofAdd (1 : ZHat)) ^ n` for some `n > 0`, and
  `D.frobeniusExponent K L hLK σ` (M014.012, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`), the
  exponent `n` chosen from that existence proof;
- `D.maximalUnramifiedField L` (M029.016, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`), the closed
  subgroup `D.fieldInertia L = L ⊓ D.inertia` representing the maximal
  unramified extension `\widetilde L` of `L`, and
  `FiniteIntermediateField E K` (M029.001, same module), a closed subgroup
  `P.field` with `P.above : G_E ≤ G_P`, `P.below : G_P ≤ G_K` and finite
  `G_K ⧸ G_P`;
- `CyclicCohomology.extensionSubgroup K L hLK` (M004.002, from
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  available through `open CyclicCohomology`), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G_L` as a subgroup of
  `G_K`;
- `ZHat` (from
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`),
  the profinite integers, and Mathlib's `ClosedSubgroup G`, `Nat.card` and
  `Multiplicative.ofAdd`.

The module imports
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions` and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`, which import the
other declarations above.

## Targets and complete telescopes

Each target has, before the binders shown, the binders of the source
variable line 33: implicit `{G : Type u}` and the instances `[Group G]` and
`[TopologicalSpace G]`.

```lean
def extensionInertia_commutes_of_mem_extensionSubgroupStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) (hk : k ∈ extensionSubgroup K.field L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1) : Prop :=
    (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) * q =
      q * QuotientGroup.mk k
```

M038.001: for a degree datum `D`, an abstract field `K` with finite residue
degree and a closed subgroup `L ≤ G_K` normal in `G_K`, the image in
`G_K ⧸ I_L` of an element `k` of `G_L` commutes with every element `q` of
`G_K ⧸ I_L` of normalized degree `1` (degree zero in additive notation).

```lean
def quotientPower_card_commutes_degreeZeroStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    (hPL : P.field.toSubgroup ≤ L.toSubgroup)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (q τ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτ : D.extensionNormalizedDegree K L hLK τ = 1) : Prop :=
    let n := Nat.card
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)
    q ^ n * τ = τ * q ^ n
```

M038.002: for a finite intermediate field `P` of `\widetilde L/K` with
`G_P ≤ G_L` and `G_P` normal in `G_K`, and `n = |G_K ⧸ G_P|`, the power
`q ^ n` of every element of `G_K ⧸ I_L` commutes with every element `τ` of
normalized degree `1`.

```lean
def _root_.Langlands.NYLL.PortInternal.M038.d003Statement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) : Prop :=
    D.extensionNormalizedDegree K L hLK (φ.1 ^ n) =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n
```

M038.003: for a Frobenius element `φ` with exponent `1`, the normalized
degree of `φ.1 ^ n` is `(Multiplicative.ofAdd (1 : ZHat)) ^ n`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so M038.001 and M038.002 lie
   in `Langlands.NYLL.ClassFormation.DegreeData`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order, the `let` of M038.002 and the line breaks. The proofs are
   omitted; they are separate work.
3. Name the target of the private source theorem M038.003
   `Langlands.NYLL.PortInternal.M038.d003Statement` (declared with `_root_`
   inside the namespace) and give it a docstring naming the source theorem,
   which has none.
4. Prefix the source docstrings of M038.001 and M038.002 with `Target:` and
   lower-case the first word after it; the wording and the line breaks are
   otherwise unchanged. Replace the source module docstring by a
   description of this module with a modification notice.
5. Replace the source import by the two focused published imports above.
6. Keep `universe u`, the namespaces, `open CyclicCohomology`, the
   noncomputable section, `open CategoryTheory`, `open scoped BigOperators`,
   the section and the variable line 33. Omit `open KummerTheory`: no
   declaration of that namespace is imported or used, and Lean rejects
   `open` of an unknown namespace. Omit the rest of the source file.
7. Precede each target by `set_option linter.unusedVariables false in`: the
   propositions do not mention the hypotheses `hk`, `hq` (M038.001), `hPL`,
   `hPnormal`, `hτ` (M038.002) and `hφ` (M038.003), which the linter
   reports as unused (a check without the options gave exactly these six
   warnings). The hypotheses are kept: each statement asserts its
   conclusion under them, in the source binder order. The options affect
   only those declarations.
8. No helper declaration or instance is added.

These are the exact source statements as named propositions, without
published proofs. It discharges no host class-formation, cup, transfer, Tate or reciprocity
target.

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
