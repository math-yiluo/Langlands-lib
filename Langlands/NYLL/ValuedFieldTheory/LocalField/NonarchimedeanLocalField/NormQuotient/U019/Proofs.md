# Equality of norm classes

The theorem `Langlands.NYLL.LocalFieldTheory.normClass_eq_iff_div_mem`
proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqIffDivMemStatement.{u}`.
This is the proof of M093.019 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the published U019 Statements module.

## Complete target

The entire unapplied theorem type is `NormClassEqIffDivMemStatement.{u}`.
It has no external term parameters. Unfolding the proposition gives

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔ x / y ∈ localNormSubgroup K L
```

The sole universe parameter `u` is arbitrary and shared by `K` and `L`;
it is not specialized to universe zero. All seven term binders remain
inside the proposition, in their original order and kinds:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `K : Type u` | explicit |
| 2 | `L : Type u` | explicit |
| 3 | `[Field K]` | instance-implicit |
| 4 | `[Field L]` | instance-implicit |
| 5 | `[Algebra K L]` | instance-implicit |
| 6 | `x : Kˣ` | explicit |
| 7 | `y : Kˣ` | explicit |

The left side is equality in the named `NormQuotient K L`.
The right side is membership in a subgroup of `Kˣ`, with division
in the specified order `x / y`. Both directions are proved:
equal classes imply this membership, and this membership implies
equal classes. Clients apply `normClass_eq_iff_div_mem K L x y`,
using `.1` and `.2` for the respective directions.

## Actual norm image and quotient

The imported constructions are unchanged:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

Thus `normUnits K L` maps extension units `Lˣ` to base-field units
`Kˣ` by the actual algebra norm. Membership of `x / y` in its image
means that some `z : Lˣ` satisfies `normUnits K L z = x / y`.
The named quotient is the quotient of `Kˣ` by this actual image,
and the canonical class map is `QuotientGroup.mk'` expressed through
the named quotient. Its commutative group structure is the published
`normQuotientCommGroup K L`.

The unrestricted field/algebra hypotheses are preserved. There is no
finite-dimensionality, finite-module, separability, Galois, local-field,
valuation, topology or surjectivity premise. In the approved Mathlib,
`Algebra.norm` is the determinant of multiplication
(`Mathlib/RingTheory/Norm/Defs.lean:59–62`), and
`Algebra.norm_eq_one_of_not_module_finite` at lines 76–79 makes it
constantly `1` outside finite modules. This convention remains included:
in that case the image subgroup is the identity subgroup, and the
same generic quotient equality criterion still applies.

## Implemented proof

The proof retains the source route after introducing the closed
proposition's seven internal binders:

```lean
intro K L _ _ _ x y
let N := localNormSubgroup K L
exact QuotientGroup.eq_iff_div_mem (N := N)
```

The three anonymous binders introduce the two field structures and
the algebra structure as local instances. The local abbreviation `N`
is the actual norm image subgroup. Mathlib's
`QuotientGroup.eq_iff_div_mem`, in the approved
`Mathlib/GroupTheory/QuotientGroup/Defs.lean:146–149`, states that
the classes of two elements of a group modulo a normal subgroup
are equal exactly when their quotient belongs to that subgroup.
Here the group is `Kˣ`; its commutativity supplies normality of `N`.
The named quotient and class map reduce to the concrete quotient
and its canonical map, so the generic equivalence has exactly the
required conclusion, including division `x / y`. It proves both
directions at once. The imported identity-class criterion from
M093.018 is not used in this proof.

## Original passage and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact source passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:183–190`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L183-L190):
the docstring is line 183, the telescope lines 184–185,
the equivalence lines 186–187, and the proof lines 188–190.
The complete original file was read and has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Its quotient constructions are at lines 26–54.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normClass_eq_iff_div_mem` | `normClass_eq_iff_div_mem`, the theorem introduced here |
| That theorem's telescope and conclusion | Existing closed `NormClassEqIffDivMemStatement` |
| `normUnits` | Existing `normUnits` |
| `localNormSubgroup` | Existing `localNormSubgroup` |
| `NormQuotient` | Existing `NormQuotient` |
| `normQuotientCommGroup` | Existing `normQuotientCommGroup` |
| `normClass` | Existing `normClass` |

Only the first row adds a declaration. Worker 107's changes on
1 November 2026 add the namespace prefix, replace the original imports
with the sole U019 Statements import, use the closed published
proposition as the theorem's type and introduce its seven internal
binders, and omit the noncomputable section, unused universe `v`
and all other declarations. The original theorem name, docstring,
local abbreviation and quotient criterion application are retained.
M093 has no compatibility change in the feasibility patch10.
Worker 1153 authored the imported statement pair. No imported pair
is edited and no worker proof draft was reused.

The original is retained in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No source-ID erratum exists in the checked workspace, project or
supplied Library locations. The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`;
upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and scope

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, Apache-2.0, author Naganori
Yamaguchi (assisted by OpenAI Codex). The Lean file includes the
dated modification record. The inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
unchanged in `repository_paths`, with respective SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Both match the retained originals. The inherited NOTICE's
ValuedFieldTheory list has no NormQuotient-specific third-party entry;
all dependency attribution is preserved. No Mathlib source is copied.

M093.020 and later units remain separate. This generic algebraic
criterion supplies no named Artin kernel or surjectivity theorem,
host quotient or evaluation adapter, or topology result.
Parent `1cbd1968-d285-4b34-822c-f6b5599d1c38` retains those obligations.
Development compilation, formal proof validation, independent semantic
acceptance and Integrator publication are distinct stages.
