# NYLL M026.008 and M026.010: absolute conjugate cosets and the conjugated absolute norm

The paired Lean file adapts the statements of two theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`.
The pinned source file has SHA-256
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.` | Docstring | Attribute | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- | --- | --- |
| M026.008 | `absoluteConjugateCosetEquiv_mk` | 132–135 | 136 | 137–142 | 142–143 | `absoluteConjugateCosetEquiv_mkStatement` |
| M026.010 | `relativeNorm_absoluteConjugate_apply` | 173–176 | none | 177–202 | 202–245 | `relativeNorm_absoluteConjugate_applyStatement` |

The source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (line 18), `open CyclicCohomology` (line 20),
`noncomputable section` (line 24), `open scoped BigOperators Pointwise`
(line 26) and the variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 29, after
the comment line 28). The source imports are the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation` and
`Nyll.GaloisCohomology.GroupTheory.QuotientTower` (lines 7–8). The other
declarations of the source file are outside this contribution.

The statements use these declarations:

- `absoluteConjugateCosetEquiv K σ` (M026.007, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Definitions`, contributed together
  with this module), the equivalence of the absolute coset spaces
  `G ⧸ G_{K^σ}` and `G ⧸ G_K` induced by `x ↦ σ * x * σ⁻¹`;
- `conjugateFixedElement A K σ a` (M026.003, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions`, contributed
  together with this module), the right conjugate `A.ρ σ⁻¹ a.1` of `a`;
- `Langlands.NYLL.PortInternal.M026.d005 σ` (M026.005, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`), the published name of the private
  source definition `absoluteConjugationEquiv`: the equivalence of
  `(baseField G).toSubgroup` with itself sending `x` to `σ * x.1 * σ⁻¹`, with
  inverse `x ↦ σ⁻¹ * x.1 * σ`;
- `relativeNorm A K L hLK` (M024.009, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`), for `hLK : G_L ≤ G_K` and
  finite `G_K ⧸ G_L`, the additive homomorphism
  `ambientFixedAddSubgroup A L →+ ambientFixedAddSubgroup A K` given by the
  sum of `A.ρ k a` over representatives `k` of the cosets of `G_L` in
  `G_K`;
- `baseField G` (M010.003, from `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`), the closed
  subgroup `⊤` of `G`, the distinguished base field, and `le_baseField K`
  (M010.005, proved in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`), whose type
  `le_baseFieldStatement K` is `K.toSubgroup ≤ (baseField G).toSubgroup`;
- `CyclicCohomology.extensionSubgroup K L hLK` (M004.002, from
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  available through `open CyclicCohomology`), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G_L` as a subgroup of
  `G_K`;
- `conjugateClosedSubgroup K σ` (M026.001, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`), the closed subgroup of `G` whose
  underlying subgroup is `ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, that is
  `σ⁻¹ G_K σ`, the subgroup of the right conjugate field `K^σ`;
- `IntegralRepGroupType` (M002.001, from
  `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`), the
  abbreviation `Type 0`, used because Mathlib's `Rep ℤ G` fixes the acting
  group to universe zero;
- `KummerTheory.ambientFixedAddSubgroup A H` (M023.001, from
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`,
  available through `open KummerTheory`), the additive subgroup
  `{a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}` of `A.V`, the elements of the
  representation `A : Rep ℤ G` fixed by the closed subgroup `H`, that is
  `A_H`;
- Mathlib's `ClosedSubgroup G`, with its underlying subgroup
  `K.toSubgroup`, and Mathlib's `Rep ℤ G`, with the underlying group `A.V`
  and the action `A.ρ`.

The module imports `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Definitions`,
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions` and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`.

## Targets and complete telescopes

M026.008 binds its own `{G : Type*}`, which shadows the variable of line 29,
so its telescope is complete as shown.

```lean
def absoluteConjugateCosetEquiv_mkStatement
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G)
    (x : (baseField G).toSubgroup) : Prop :=
    absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) =
      QuotientGroup.mk (Langlands.NYLL.PortInternal.M026.d005 σ x)
```

The equivalence `absoluteConjugateCosetEquiv K σ` sends the coset of `x` to
the coset of `PortInternal.M026.d005 σ x`, the element `σ * x.1 * σ⁻¹`. The
source proof is `rfl`.

M026.010 has, before the binders shown, the binders of the source variable
line 29: implicit `{G : IntegralRepGroupType}` and the instances `[Group G]` and
`[TopologicalSpace G]`.

```lean
def relativeNorm_absoluteConjugate_applyStatement [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    [Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))]
    (a : ambientFixedAddSubgroup A K) : Prop :=
    letI : Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G)
            (conjugateClosedSubgroup K σ)
            (le_baseField (conjugateClosedSubgroup K σ))) :=
      Finite.of_equiv
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) K
            (le_baseField K))
        (absoluteConjugateCosetEquiv K σ).symm
    ((relativeNorm A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) :
      ambientFixedAddSubgroup A (baseField G)) : A.V) =
      A.ρ σ⁻¹
        ((relativeNorm A (baseField G) K
          (le_baseField K) a :
          ambientFixedAddSubgroup A (baseField G)) : A.V)
```

Assume `G_K` has finite index in `G` (the instance binder). The `letI`
supplies the finiteness of the coset space of `G_{K^σ}`, transported along
`(absoluteConjugateCosetEquiv K σ).symm`, which `relativeNorm` over
`conjugateClosedSubgroup K σ` requires. The proposition states that the
absolute norm of the right conjugate `a^σ = conjugateFixedElement A K σ a`
from `A_{K^σ}` to `A_G` has underlying element `A.ρ σ⁻¹` applied to the
underlying element of the absolute norm of `a` from `A_K`: the absolute norm
commutes with conjugation.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ClassFormation`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order, the `letI` of M026.010 and the line breaks, except that M026.008
   refers to the private source definition `absoluteConjugationEquiv`
   (M026.005) by its published name `Langlands.NYLL.PortInternal.M026.d005`.
   The proofs and the `@[simp]` attribute of M026.008, which does not apply
   to a definition of a proposition, are omitted; the proofs are separate
   work.
3. Prefix the source docstrings with `Target:` and lower-case the first
   word after it; the wording is otherwise unchanged and the lines are
   rewrapped, except that the docstring of M026.008 adds that
   `absoluteConjugationEquiv` is published as
   `Langlands.NYLL.PortInternal.M026.d005`. Replace the source module
   docstring by a description of this module with a modification notice.
4. Replace the source imports by the three focused imports above.
5. Keep the namespace, both opens, the noncomputable section,
   `open scoped BigOperators Pointwise`, the comment line 28 and the variable
   line 29; omit the rest of the source file.
6. No helper declaration, instance or linter option is added. The private
   source theorem `relativeCosetAction_absoluteConjugate` (M026.009, lines
   145–171),
   used only by the source proof of M026.010, is not part of this module.

This is the exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate or reciprocity
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
