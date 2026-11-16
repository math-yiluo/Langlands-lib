# The Herbrand quotient is the cardinality ratio

This module proves the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_eq_card_ratio`, the proof phase of
M118.002 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m118).
Its type is the published proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_eq_card_ratioStatement` applied to the
theorem's parameters:

```lean
theorem herbrandQuotient_eq_card_ratio (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)] :
    herbrandQuotient_eq_card_ratioStatement (G := G) (A := A) σ
```

## Target and binders

The section variables are those of the published statement module and the source: `universe uG uA uB uC`, `{G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}`, `[Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]` and the actions `[MulDistribMulAction G A]` (and of `G` on `B` and `C`), in `namespace ProfiniteCohomology.Herbrand`; only those on which the theorem depends are included. The theorem takes `σ` and the two finiteness instances, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Statements`, the target is the proposition

```lean
herbrandQuotient (G := G) (A := A) σ =
  (Nat.card (HerbrandH0 G A) : ℚ) /
    (Nat.card (HerbrandHMinusOne G A σ) : ℚ)
```

Here `G` is a finite group acting on the commutative group `A` by multiplicative automorphisms, `σ : G`, and `HerbrandH0 G A` (M113.028) and `HerbrandHMinusOne G A σ` (M113.029) are the low-degree Tate quotients `A^G / N_G A` and `ker N_G / I_G A` (with `I_G A` the image of `a ↦ a^(σ-1)`). `herbrandQuotient (G := G) (A := A) σ` (M118.001) is the rational number `#H⁰ / #H⁻¹`, defined under finiteness instances for both quotients. The target says that the Herbrand quotient is `#H⁰ / #H⁻¹`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Statements`, which defines the targets and imports `herbrandQuotient` (M118.001) and, through the published `Basic.HerbrandQuotients.Definitions` module, `HerbrandH0`, `HerbrandHMinusOne` and the subgroups `fixedSubgroup`, `tateNormSubgroup`, `normKernelSubgroup` and `augmentationSubgroup` (M113.003, M113.021–.023), with the instances making the quotients finite for a finite module.

The module opens `BigOperators` scoped, as the source and the published statement module do.

## Implemented proof

After `show` states the published proposition unfolded, the proof is the source proof `rfl`: `herbrandQuotient` is defined (M118.001) as this ratio.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`, lines 41–47](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean#L41-L47):
the docstring at line 41 and the theorem at lines 42–47. It lies in `namespace CyclicCohomology` (line 18), its `noncomputable section` (line 20) with `open scoped BigOperators` (line 22), `namespace ProfiniteCohomology` and `namespace Herbrand` (lines 24–25), after `universe uG uA uB uC` (line 27), with the variables of lines 29–32. The source is:

```lean
/-- The Herbrand quotient is definitionally the ratio `#H⁰ / #H^{-1}`. -/
theorem herbrandQuotient_eq_card_ratio (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)] :
    herbrandQuotient (G := G) (A := A) σ =
      (Nat.card (HerbrandH0 G A) : ℚ) /
        (Nat.card (HerbrandHMinusOne G A σ) : ℚ) :=
  rfl
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`;
its SHA-256 is `53b28b77b5f5f3450745dd1ea265858d605ea582e41d537d690f1bd1736aee58`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `herbrandQuotient_eq_card_ratioStatement (G := G) (A := A) σ` as its type, and begin the proof with `show` stating it unfolded; the source's term proof `rfl` is kept as the tactic `rfl`;
- omit all other source declarations.

The theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. Worker 5264 prepared this module as revision 1 of the shared draft of Task 7142 (`8a2f229a-7526-448d-b445-2324316ba3ce`); Worker 749, the task's executor, rechecked it in the approved environment and submitted it unchanged apart from this sentence, with Worker 5264 as coauthor. The unchanged
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M118.002. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
