# Norm classes of extension-unit norms

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.mk_normUnits_eq_one`.
Its complete unapplied type is the already published closed proposition
`Langlands.NYLL.LocalFieldTheory.MkNormUnitsEqOneStatement.{u}`.
This is the proof phase of M093.017 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

## Closed target and binders

The target internally quantifies over exactly this telescope and conclusion:

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ),
  normClass K L (normUnits K L x) = 1
```

All six term binders are inside the closed proposition, in this order:

| Binders | Kind | Meaning |
| --- | --- | --- |
| `K`, `L` | explicit, each `Type u` | Base field and extension field |
| `[Field K]`, `[Field L]` | instance-implicit | The two field structures |
| `[Algebra K L]` | instance-implicit | The specified algebra structure |
| `x : Lˣ` | explicit | An arbitrary unit of the extension field |

The conclusion is an equation in `NormQuotient K L`. The left side sends
`x` to the base-field unit `normUnits K L x : Kˣ` and takes its class
`normClass K L (normUnits K L x)`. The right side `1` is the identity of
the published group structure `normQuotientCommGroup K L`. The norm
runs from extension units `Lˣ` to base units `Kˣ`. The single universe
parameter `u` is arbitrary and is shared by `K` and `L`; it is not
restricted to zero. The theorem has no external term parameters, and a
client applies it as `mk_normUnits_eq_one K L x`. It adds no hypothesis:
no finite-dimensionality, finite-module condition, separability, Galois
property, local-field structure, valuation, topology or surjectivity
assumption.

The sole direct import is the published U017 Statements module. Through
its U016 Proofs import it keeps the published `M093.016.END` boundary and
the unchanged named constructions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

So `normUnits K L : Lˣ →* Kˣ` is the actual unit norm, the subgroup is
its actual range in `Kˣ`, `NormQuotient K L` is the named quotient of
`Kˣ` by that range, and `normClass K L` is the canonical quotient
homomorphism, defined as `QuotientGroup.mk' (localNormSubgroup K L)`.
The norm is Mathlib's unrestricted `Algebra.norm K`. By
`Algebra.norm_eq_one_of_not_module_finite` it is constantly `1` when `L`
is not a finite `K`-module. Then `normUnits K L x = 1`, the norm image is
trivial, and the theorem still covers that case.

## Implemented proof

The proof introduces the target's six binders, naming the three instances
anonymously, then applies the original one-line proof at line 174
unchanged:

```lean
intro K L _ _ _ x
exact (QuotientGroup.eq_one_iff (normUnits K L x)).2 ⟨x, rfl⟩
```

Mathlib's `QuotientGroup.eq_one_iff`, in the approved
`Mathlib/GroupTheory/QuotientGroup/Defs.lean` at lines 119–122, states
that for a normal subgroup `N` of a group `G` and `g : G`, the coercion
`(g : G ⧸ N)` equals `1` exactly when `g ∈ N`. Here `G` is `Kˣ`, `N` is
`localNormSubgroup K L`, which is normal because `Kˣ` is commutative, and
`g` is `normUnits K L x`. The goal `normClass K L (normUnits K L x) = 1`
is definitionally that coercion equation: `normClass K L` unfolds to
`QuotientGroup.mk' (localNormSubgroup K L)`, and the `1` of
`normQuotientCommGroup K L` is the quotient group's identity. The
backward direction therefore reduces the goal to
`normUnits K L x ∈ localNormSubgroup K L`. That subgroup is
`(normUnits K L).range`, whose membership unfolds to
`∃ y, normUnits K L y = normUnits K L x`. The anonymous constructor
`⟨x, rfl⟩` supplies the range witness `y = x`, with `rfl` proving the
equation.

The proof uses no choice construction of its own and does not use
`normQuotientConcreteEquiv` or `NormQuotient.inductionOn`. The published
statement already depends on `propext`, `Classical.choice` and
`Quot.sound` through its imported definitions; the proof adds no further
axiom.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 171–174](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L171-L174):
the docstring at 171, the theorem name and telescope at 172, the equation
at 173 and the proof at 174. The original reads:

```lean
/-- The quotient class of any extension-unit norm is the identity norm class. -/
theorem mk_normUnits_eq_one (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) :
    normClass K L (normUnits K L x) = 1 := by
  exact (QuotientGroup.eq_one_iff (normUnits K L x)).2 ⟨x, rfl⟩
```

The complete original file was read and its SHA-256 verified as
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The unit norm `normUnits` comes from the source file
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, lines 32–34 (SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`),
already published as NYLL unit M092.002.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `LocalFieldTheory.mk_normUnits_eq_one` (theorem) | `mk_normUnits_eq_one` (theorem), proving the closed published target |
| Same theorem's statement | Existing `MkNormUnitsEqOneStatement` |
| `LocalFieldTheory.normUnits` | Existing `normUnits` |
| `LocalFieldTheory.localNormSubgroup` | Existing `localNormSubgroup` |
| `LocalFieldTheory.NormQuotient` | Existing `NormQuotient` |
| `LocalFieldTheory.normQuotientCommGroup` | Existing `normQuotientCommGroup` |
| `LocalFieldTheory.normClass` | Existing `normClass` |

Only the first row introduces a declaration here. Modifications by
Worker 248 on 31 October 2026 are: add the `Langlands.NYLL` namespace
prefix; replace the source imports with the sole U017 Statements import;
give the theorem the closed published proposition as its type and
introduce its six internal binders; omit the noncomputable section, the
unused universe `v` and all other source declarations. The original
theorem name, its docstring and the proof term are kept. The partition
records no patch10 change to this original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable source-ID erratum exists in the workspace, project or
current Library. A TaskHub search and exact-name searches of the current
Library, staging and shared drafts found no earlier proof port. The only
other copies of the original passage are old upstream audit drafts,
which were not reused.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; the original proof needed no
change for the approved environment. A development check compiled the
module with no diagnostics. It found a theorem with level parameter `u`
whose unapplied type is the constant
`MkNormUnitsEqOneStatement.{u}`, using only `propext`,
`Classical.choice` and `Quot.sound`. This check does not establish
independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 248 adapted this proof directly from
the pinned original and wrote this companion; Worker 248 also authored
the published statement. No other project worker supplied code or a
reused draft for this proof. The statement and the imported
constructions are used unchanged; all imported Library modules and their
paired Markdown remain frozen.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The inherited NOTICE has no NormQuotient-specific third-party entry, and
all inherited dependency notices remain intact. No Mathlib code is
copied into this file.

This generic quotient identity supplies no Artin map, Artin kernel or
surjectivity result, host quotient or evaluation adapter, or topology
theorem. M093.018 and later source units remain separate, and parent
finite reciprocity task `1cbd1968-d285-4b34-822c-f6b5599d1c38` remains
open.
