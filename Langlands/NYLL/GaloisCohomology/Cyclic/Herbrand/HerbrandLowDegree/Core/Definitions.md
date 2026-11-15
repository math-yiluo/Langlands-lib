# NYLL M118.001: the Herbrand quotient

The paired Lean file adapts one definition of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`.
The pinned source file has SHA-256
`53b28b77b5f5f3450745dd1ea265858d605ea582e41d537d690f1bd1736aee58`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `CyclicCohomology.ProfiniteCohomology.Herbrand.` | Docstring | Definition | Adapted name after `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.` |
| --- | --- | --- | --- | --- |
| M118.001 | `herbrandQuotient` | 34–36 | 37–39 | `herbrandQuotient` |

The source imports
`Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic` and
`Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality`
(lines 7–8). The source context, copied verbatim, is
`namespace CyclicCohomology` (line 18), `noncomputable section` (line 20),
`open scoped BigOperators` (line 22), `namespace ProfiniteCohomology` and
`namespace Herbrand` (lines 24–25), `universe uG uA uB uC` (line 27), the
variable lines 29–32

```lean
variable {G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]
```

and the closing lines 120–124. The other declarations of the source file
(the four theorems M118.002–.005 of lines 41–118) are not part of this
module; their statements are in the companion module
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Statements`.

The definition uses Mathlib's `Finite`, `Nat.card` and the rationals `ℚ`,
and the NYLL types `HerbrandH0` (M113.028), the quotient of the `G`-fixed subgroup of `A` by
the norm subgroup, and `HerbrandHMinusOne` (M113.029), the quotient of the
norm kernel by the augmentation subgroup for the generator `σ`, both in
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` and published in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`.

## Definition and complete telescope

Lean includes only the variables the definition uses, so its elaborated
telescope is `{G : Type uG} {A : Type uA} [Group G] [Fintype G]
[CommGroup A] [MulDistribMulAction G A]` followed by the binders shown, with
value in `ℚ`.

### M118.001

```lean
noncomputable def herbrandQuotient (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)] : ℚ :=
  (Nat.card (HerbrandH0 G A) : ℚ) / (Nat.card (HerbrandHMinusOne G A σ) : ℚ)
```

The Herbrand quotient of `A` for the generator `σ` is the rational number
`#H⁰(G, A) / #H⁻¹(G, A)`. The finiteness instances keep `Nat.card` from
taking the value `0` on an infinite quotient. The docstring, including its
opening words "Herbrand-quotient theory the Herbrand-quotient definition",
is the source docstring verbatim.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition lies in
   `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand`.
2. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition. The declaration,
   its docstring and its body are copied verbatim, with the source line
   breaks.
3. Replace the two source imports by `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`, which publishes
   `HerbrandH0` and `HerbrandHMinusOne`.
4. Omit the other declarations of the source file (listed above). The
   namespaces, the noncomputable section, the scoped open, the universe
   declaration and the variable lines are kept unchanged.
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
