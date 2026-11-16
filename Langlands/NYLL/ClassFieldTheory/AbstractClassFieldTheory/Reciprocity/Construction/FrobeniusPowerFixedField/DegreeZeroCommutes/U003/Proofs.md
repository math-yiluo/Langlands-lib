# Normalized degrees of powers of a degree-one Frobenius element

This module proves the theorem
`Langlands.NYLL.PortInternal.M038.d003`, the proof phase of
M038.003 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m038).
Its type is the published proposition
`Langlands.NYLL.PortInternal.M038.d003Statement` applied to the
theorem's parameters:

```lean
theorem _root_.Langlands.NYLL.PortInternal.M038.d003 (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) :
    Langlands.NYLL.PortInternal.M038.d003Statement D K L hLK φ hφ n
```

## Target and binders

The section variables are those of the published statement module and the source: `universe u` and `{G : Type u} [Group G] [TopologicalSpace G]`, in `section degreeOnePowerFields` and `namespace DegreeData`. The theorem takes `D`, `K`, `L`, `hLK`, `hLnormal`, `φ`, `hφ` and `n`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.Statements`, the target is the proposition

```lean
D.extensionNormalizedDegree K L hLK (φ.1 ^ n) =
  (Multiplicative.ofAdd (1 : ZHat)) ^ n
```

Here `D : DegreeData G` (M010.002) is a degree datum, a continuous homomorphism `D.degree` from `G` onto the profinite integers written multiplicatively; `K : FiniteResidueAbstractField D` (M010.021) is an abstract field `K.field` with finite residue quotient; `L` is a closed subgroup with `hLK : L ≤ K.field` such that `extensionSubgroup K.field L hLK` (M004.002, the subgroup `L` of `K.field` as a subgroup of `K.field`) is normal. `D.fieldInertiaWithin K.field` (M010.014) is the kernel of the degree restricted to `K.field`, the inertia subgroup `I_K`; `D.extensionInertiaWithin K.field L hLK` (M012.002) is `L ∩ I_K` inside `K.field`, so that the quotient `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` is the group `G(\widetilde L/K)`; and `D.extensionNormalizedDegree K L hLK` (M012.005) is the normalized degree `D.normalizedDegree K` (M011.006) of `K.field` factored through this quotient. `φ : D.FrobeniusElements K L hLK` (M012.009) is an element of `G(\widetilde L/K)` together with a proof that its normalized degree is `(ofAdd 1) ^ m` for some `m > 0`, and `D.frobeniusExponent K L hLK φ` (M014.012) is the chosen exponent `m`; `hφ` says that it is `1`. The target says that the normalized degree of `φ ^ n` is `(ofAdd 1) ^ n` for every natural `n`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.Statements`, which defines the targets and imports, through the published `FrobeniusClosure.Definitions` and `NormSubgroup.Definitions` modules, `DegreeData` (M010.002), `FiniteResidueAbstractField` (M010.021), `fieldInertiaWithin` (M010.014) with its normality instance (M010.015), `extensionInertiaWithin` (M012.002), `extensionNormalizedDegree` (M012.005), `FrobeniusElements` (M012.009), `frobeniusExponent` (M014.012), `FiniteIntermediateField` (M029.001), `maximalUnramifiedField` (M029.016) and `extensionSubgroup` (M004.002).

The module opens `CyclicCohomology`, as the source does, for `extensionSubgroup` in the normality binder; the source's `open KummerTheory`, `open CategoryTheory` and `open scoped BigOperators` are not needed, since none of their names or notation occur in the statement or the proof.

## Implemented proof

After `show` states the published proposition unfolded, the proof states as the local fact `hfrob` that the normalized degree of `φ.1` is `(ofAdd 1)` to the power `D.frobeniusExponent K L hLK φ`; it is `(Exists.choose_spec φ.2).2`, since the exponent is by definition (M014.012) `Exists.choose φ.2`. This is the statement of the source lemma M014.014 `extensionNormalizedDegree_frobenius_eq_pow`, whose proof is not yet in the Library. The rest is the source proof with `hfrob` in place of that lemma: `rw [map_pow, hfrob, hφ, pow_one]` turns the goal into `(ofAdd 1) ^ n = (ofAdd 1) ^ n`, which `rw` closes by reflexivity.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`, lines 128–138](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean#L128-L138):
the private theorem `DegreeData.extensionNormalizedDegree_pow_of_degreeOne` at lines 128–138, which has no docstring. It lies in `namespace ClassFormation` (line 19), with `open KummerTheory` (line 21) and `open CyclicCohomology` (line 22), after `universe u` (line 17), in its `noncomputable section` (line 26) with `open CategoryTheory` (line 28) and `open scoped BigOperators` (line 29), `section degreeOnePowerFields` (line 31), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 33) and `namespace DegreeData` (line 35). The source is:

```lean
private theorem extensionNormalizedDegree_pow_of_degreeOne (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) :
    D.extensionNormalizedDegree K L hLK (φ.1 ^ n) =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
  rw [map_pow,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ, pow_one]
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`;
its SHA-256 is `4f9719760da9ac7344ece27b3aaf46d4acbd1d1295202dbb9eb84b41bc9b4256`.

Modifications by Worker 5264 on 15 November 2026:

- replace the source imports by the Library import listed above;
- publish the private theorem under the name `Langlands.NYLL.PortInternal.M038.d003` (declared with `_root_` inside `namespace DegreeData`), with a docstring naming the source theorem, give it the published proposition `Langlands.NYLL.PortInternal.M038.d003Statement D K L hLK φ hφ n` as its type, and begin the proof with `show` stating it unfolded;
- rewrite with the local fact `hfrob`, proved by `(Exists.choose_spec φ.2).2`, in place of the source's `D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ`;
- omit `open KummerTheory`, `open CategoryTheory`, `open scoped BigOperators` and all other source declarations.

The binders and the remaining proof steps are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M038.003. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
