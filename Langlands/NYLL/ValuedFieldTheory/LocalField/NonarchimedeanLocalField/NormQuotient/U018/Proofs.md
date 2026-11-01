# Identity norm classes and extension-unit norms

The theorem `Langlands.NYLL.LocalFieldTheory.normClass_eq_one_iff`
proves the already published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqOneIffStatement.{u}`.
This is the proof of M093.018 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
The sole direct import is the published U018 Statements module.

## Complete target

The entire unapplied theorem type is `NormClassEqOneIffStatement.{u}`:
there are no external term parameters. Unfolding that proposition gives

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
  normClass K L x = 1 ↔ ∃ y : Lˣ, normUnits K L y = x
```

The single universe parameter `u` is arbitrary and shared by `K` and
`L`. The six internal term binders retain the source order and kinds:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `K : Type u` | explicit |
| 2 | `L : Type u` | explicit |
| 3 | `[Field K]` | instance-implicit |
| 4 | `[Field L]` | instance-implicit |
| 5 | `[Algebra K L]` | instance-implicit |
| 6 | `x : Kˣ` | explicit |

Both directions of the equivalence are proved. The left equation lies
in the named `NormQuotient K L`, with the identity supplied by the
published `normQuotientCommGroup K L`. On the right, the witness
`y : Lˣ` is an extension-field unit, and `normUnits K L y = x` is an
equation in `Kˣ`, in precisely this order. Clients apply the theorem
as `normClass_eq_one_iff K L x`; `.1` extracts a norm witness from an
identity class and `.2` produces an identity class from a norm witness.

Through U018 Statements, the proof uses these existing constructions
without changing their Lean or Markdown:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

The canonical map `normClass` is `QuotientGroup.mk'` on this concrete
quotient. The subgroup is the actual range of the actual unit norm.
There is no finite-dimensionality, finite-module, separability, Galois,
local-field, valuation, topology or surjectivity assumption. Mathlib's
`Algebra.norm_eq_one_of_not_module_finite` (approved
`Mathlib/RingTheory/Norm/Defs.lean:76–79`) makes the underlying norm
constantly `1` outside finite modules; that case remains included.
In that case the norm-witness condition holds exactly when `x = 1`,
since every unit norm is `1` and the extension has its identity unit.

## Implemented proof

The proof follows the original two-line route after introducing the
closed proposition's binders:

```lean
intro K L _ _ _ x
rw [← MonoidHom.mem_range]
exact QuotientGroup.eq_one_iff x
```

The three anonymous binders introduce the two field structures and
the algebra structure as local instances. Mathlib's
`MonoidHom.mem_range`, at approved
`Mathlib/Algebra/Group/Subgroup/Ker.lean:77–79`, identifies membership
in a homomorphism's range with the existence of a preimage, by
`Iff.rfl`. Rewriting backwards turns
`∃ y : Lˣ, normUnits K L y = x` into
`x ∈ (normUnits K L).range`.

Mathlib's `QuotientGroup.eq_one_iff`, at approved
`Mathlib/GroupTheory/QuotientGroup/Defs.lean:119–122`, states
`(x : G ⧸ N) = 1 ↔ x ∈ N` for a normal subgroup `N`.
Here `G = Kˣ` and `N = localNormSubgroup K L`; commutativity of
`Kˣ` supplies normality. The named subgroup unfolds to
`(normUnits K L).range`, while the named quotient, its identity and
the canonical class map unfold to the quotient-group operations in
that fact. Its equivalence is therefore exactly the rewritten goal.
This proves both directions at once. The preceding theorem
`mk_normUnits_eq_one` is imported but is not used in this proof.

## Original passage and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact source passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:176–181`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L176-L181):
the docstring is line 176, the name and telescope lines 177–178,
the equivalence line 179, and the proof lines 180–181.
The two proof lines are exactly the `rw` and `exact` lines above.
The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normClass_eq_one_iff` | `normClass_eq_one_iff`, the theorem introduced here |
| That theorem's telescope and conclusion | Existing closed `NormClassEqOneIffStatement` |
| `normUnits` | Existing `normUnits` |
| `localNormSubgroup` | Existing `localNormSubgroup` |
| `NormQuotient` | Existing `NormQuotient` |
| `normQuotientCommGroup` | Existing `normQuotientCommGroup` |
| `normClass` | Existing `normClass` |

Only the first row adds a declaration. Worker 107's changes on
31 October 2026 are to add the namespace prefix, replace the original
imports with U018 Statements, use the closed published proposition
as the theorem's type and introduce its six internal binders, and omit
the noncomputable section, unused universe `v` and all other source
declarations. The original theorem name, docstring and two proof
lines are retained. M093 has no change in the feasibility patch10.
The imported statement was authored by Worker 248; no statement or
dependency is edited here, and no worker proof draft was reused.

The retained original is in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No source-ID erratum was found in the workspace, project or supplied
Library notes. The approved environment is Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`,
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`;
upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and scope

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, Apache-2.0, author Naganori
Yamaguchi (assisted by OpenAI Codex). The Lean file includes the dated
modification record. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths`, with respective SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
They match the retained originals. The inherited NOTICE's
ValuedFieldTheory list has no NormQuotient-specific third-party entry;
all existing dependency attribution is preserved. No Mathlib source
is copied into the proof.

M093.019 and later units remain separate. This generic algebraic
criterion supplies no named Artin kernel or surjectivity theorem,
host quotient or evaluation adapter, or topology result.
Parent `1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open.
Development compilation, formal proof validation, independent semantic
acceptance and Integrator publication are distinct stages.
