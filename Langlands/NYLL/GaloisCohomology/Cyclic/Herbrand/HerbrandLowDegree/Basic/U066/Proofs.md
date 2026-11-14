# The norm of a coboundary is trivial (NYLL M113.066)

This module proves the published closed proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.tateNorm_sigmaMinusOne_eq_oneStatement.{uG, uA}` by the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.tateNorm_sigmaMinusOne_eq_one.{uG, uA}`. It is the proof phase of M113.066 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m113).
For a finite group `G`, `σ : G` and `a : A`, `N_G (a^(σ-1)) = 1`; this is the calculation `N_G(b^(σ-1)) = 1` of the low-degree cyclic-cohomology exact sequence.

## Target and theorem

The sole direct import is
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements`;
it and the `Basic.Definitions` module it imports are unchanged. In namespace
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` the published target and the theorem are:

```lean
def tateNorm_sigmaMinusOne_eq_oneStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) (a : A),
    tateNorm G A (sigmaMinusOne G A σ a) = 1

theorem tateNorm_sigmaMinusOne_eq_one : tateNorm_sigmaMinusOne_eq_oneStatement.{uG, uA}
```

The theorem's unapplied type is exactly the named closed proposition, at the
theorem's own universe parameters `uG, uA` in the order in which the
statement declares them; the universes are arbitrary. The theorem has no term
parameters outside the proposition, whose eight binders are, in order:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `G : Type uG` | Implicit |
| 2 | `A : Type uA` | Implicit |
| 3 | `[Group G]` | Instance-implicit |
| 4 | `[Fintype G]` | Instance-implicit |
| 5 | `[CommGroup A]` | Instance-implicit |
| 6 | `[MulDistribMulAction G A]` | Instance-implicit |
| 7 | `σ : G` | Explicit |
| 8 | `a : A` | Explicit |

`σ` is arbitrary (no cyclicity or generator hypothesis). These are the source section variables the theorem uses, followed by its own binders: no hypothesis is added or dropped.

`tateNorm G A a` is the published `Basic.Definitions` operator `∏ g : G, g • a` (a product over `Finset.univ` of the `Fintype G`), the finite-group norm `N_G a` of a multiplicative `G`-module.

`sigmaMinusOne G A σ a` is the published `Basic.Definitions` operator `σ • a * a⁻¹`, the multiplicative coboundary `a^(σ-1)`.

`MulDistribMulAction G A` is Mathlib's action of a monoid by monoid endomorphisms (`g • (x * y) = g • x * g • y` and `g • 1 = 1`); with `Group G` each `g` acts by an automorphism.

## Implemented proof

The complete theorem is:

```lean
theorem tateNorm_sigmaMinusOne_eq_one :
    tateNorm_sigmaMinusOne_eq_oneStatement.{uG, uA} := by
  intro G A _ _ _ _ σ a
  have hshift : (∏ g : G, (g * σ) • a) = ∏ g : G, g • a := by
    exact Fintype.prod_equiv (Equiv.mulRight σ)
      (fun g : G => (g * σ) • a) (fun g : G => g • a) (by intro g; rfl)
  calc
    tateNorm G A (sigmaMinusOne G A σ a) = ∏ g : G, ((g * σ) • a) * (g • a)⁻¹ := by
      unfold tateNorm sigmaMinusOne
      apply Finset.prod_congr rfl
      intro g _hg
      calc
        g • (σ • a * a⁻¹) = g • (σ • a) * g • a⁻¹ :=
          MulDistribMulAction.smul_mul g (σ • a) a⁻¹
        _ = (g * σ) • a * (g • a)⁻¹ := by
          rw [← SemigroupAction.mul_smul, smul_inv']
    _ = (∏ g : G, (g * σ) • a) * ∏ g : G, (g • a)⁻¹ := by
      exact Finset.prod_mul_distrib
    _ = 1 := by
      rw [hshift, Finset.prod_inv_distrib, mul_inv_cancel]
```

`intro` introduces all eight binders; the rest is the unchanged source proof.

* `hshift`: reindexing by right multiplication, `∏ g, (g * σ) • a = ∏ g, g • a`, by Mathlib's `Fintype.prod_equiv` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:742`) with the permutation `Equiv.mulRight σ` (`g ↦ g * σ`).
* The `calc` first rewrites each factor after `unfold tateNorm sigmaMinusOne`: `g • (σ • a * a⁻¹) = g • (σ • a) * g • a⁻¹` (`MulDistribMulAction.smul_mul`) `= (g * σ) • a * (g • a)⁻¹` (`← SemigroupAction.mul_smul` and Mathlib's `smul_inv'`, `Mathlib/Algebra/Group/Action/Basic.lean:204`).
* It splits the product with `Finset.prod_mul_distrib` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:310`).
* Finally `hshift`, `Finset.prod_inv_distrib` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:675`) and `mul_inv_cancel` give `N_G a * (N_G a)⁻¹ = 1`.

Dependencies are Mathlib and the published `Basic.Definitions`/`Basic.Statements`
modules only. No auxiliary declaration, instance, attribute or `open` is added.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean:770–790`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean#L770-L790)
(partition unit lines 772–792). The source theorem is at lines 772–773 (docstring at lines 770–771; no `omit`) and its proof at lines 774–790. The section variables are at
lines 62–64 and `tateNorm`/`sigmaMinusOne` at lines 37–45. The complete original
file was read; its SHA-256 is
`ae3b4a25fca38258f0d349502812a9500f24049a7497f3bc971482b26bd397b9`.

| Original in `CyclicCohomology.ProfiniteCohomology.Herbrand` | Adapted in `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` |
| --- | --- |
| Theorem `tateNorm_sigmaMinusOne_eq_one`, lines 772–773 | `tateNorm_sigmaMinusOne_eq_one : tateNorm_sigmaMinusOne_eq_oneStatement.{uG, uA}` |
| Telescope: used section variables of lines 62–64, then `(σ : G) (a : A)` | Existing closed `tateNorm_sigmaMinusOne_eq_oneStatement` |
| Proof, lines 774–790 | Identical, preceded by one `intro` |

Only the first row adds a declaration. Worker 5424's modification (14 November
2026) adds the `Langlands.NYLL` namespace prefix, uses the published closed target
and introduces its binders, and otherwise keeps the source proof. The sole import
is the statement module in place of the source's nine Mathlib imports; the source
`noncomputable section`, section `variable`s, `omit` lines and all other source
declarations are omitted. M113 has no compatibility change in the feasibility
patch10.

The retained source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
under `n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

## Attribution, licence and environment

The Lean file keeps the original copyright, Apache-2.0 and author header verbatim
(copyright 2026 Naganori Yamaguchi; author "Naganori Yamaguchi (assisted by OpenAI
Codex)"), followed by Worker 5424's dated modification record. Worker 5424
extracted this proof directly from the pinned original and the published statement
module; no worker draft was reused and there are no project coauthors. The
unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already in
the Library and are not modified.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`); upstream used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. In this
environment the module compiles with no errors or warnings and the theorem depends
only on `propext`, `Classical.choice` and `Quot.sound`. Compilation is not
acceptance: publication under `lean.proof@1` also requires the Lake build,
exact-target and unchanged-statement checks, independent semantic review and
integration.

## Scope

This is only the norm identity. The subgroup inclusion `augmentationSubgroup_le_normKernelSubgroup` (source lines 793–797) and all Herbrand-quotient units remain separate. These support lemmas discharge no host class-formation, cup, transfer,
Tate or reciprocity target.
