# NYLL M119.001: the condition that a Herbrand quotient is defined

The paired Lean file adapts one definition of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean`.
The pinned source file has SHA-256
`28215b237d5b5024f73b33d90b059eb6273b8fc92ff3c0ae88f9f9dfb804ad27`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `CyclicCohomology.ProfiniteCohomology.Herbrand.` | Docstring | Definition | Adapted name after `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.` |
| --- | --- | --- | --- | --- |
| M119.001 | `HerbrandQuotientDefined` | 37 | 38–41 | `HerbrandQuotientDefined` |

The source imports
`Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core`,
`Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison`,
`Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic` and
`Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic`
(lines 7–10). The context of the definition is `namespace CyclicCohomology`
(line 21), `noncomputable section` (line 23), `namespace ProfiniteCohomology`
and `namespace Herbrand` (lines 25–26), `open CategoryTheory` (line 28),
`universe uG uA` (line 30) and the variable lines 32–35
(`variable {G A B C : Type}` and instance variables for them).

The definition binds its own `(G : Type uG) (A : Type uA)` and instances,
which shadow the section variables, so Lean includes none of the section
variables and its telescope is exactly the binders shown below. The other
declarations of the source file are not part of this module.

The definition uses Mathlib's `Finite` and conjunction, and the NYLL types
`HerbrandH0` (M113.028), the quotient of the `G`-fixed subgroup of `A` by
the norm subgroup, and `HerbrandHMinusOne` (M113.029), the quotient of the
norm kernel by the augmentation subgroup for the generator `σ`, both in
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` and published in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`.

## Definition

```lean
def HerbrandQuotientDefined (G : Type uG) (A : Type uA)
    [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]
    (σ : G) : Prop :=
  Finite (HerbrandH0 G A) ∧ Finite (HerbrandHMinusOne G A σ)
```

The Herbrand quotient of `A` for `σ` is defined when both low-degree groups
`H⁰(G, A)` and `H⁻¹(G, A)` are finite.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition lies in
   `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand`.
2. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition. The declaration,
   its docstring and its body are copied verbatim, with the source line
   breaks.
3. Replace the four source imports by `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`, which publishes
   `HerbrandH0` and `HerbrandHMinusOne`.
4. Omit the variable lines 32–35 (the definition uses none of their
   variables, so its telescope is unchanged), the open of `CategoryTheory`
   (none of its names occurs) and the other declarations of the source file.
   Retain the namespaces, the noncomputable section and the universe
   declaration.
5. No linter option, helper declaration or instance is added.

This is a definition only. It discharges no host Herbrand-quotient,
class-formation, Tate or reciprocity target.

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
