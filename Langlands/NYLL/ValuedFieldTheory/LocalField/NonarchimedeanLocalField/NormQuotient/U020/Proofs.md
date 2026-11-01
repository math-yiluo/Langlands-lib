# Kernel of the norm-class homomorphism

This module proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassKerStatement.{u}` by
`Langlands.NYLL.LocalFieldTheory.normClass_ker.{u}`. It is the proof
phase of M093.020 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
The kernel of the canonical homomorphism to norm classes is precisely
the actual image of the algebra norm on extension units.

## Complete target and theorem

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U020.Statements`.
The imported statement and its dependencies are unchanged. In namespace
`Langlands.NYLL.LocalFieldTheory` the complete target and theorem are:

```lean
def NormClassKerStatement.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L],
    MonoidHom.ker (normClass K L) = localNormSubgroup K L

theorem normClass_ker.{u} : NormClassKerStatement.{u}
```

The theorem's unapplied type is exactly the named closed proposition.
It has no external term parameters. Its sole universe parameter `u`
is arbitrary and shared by `K` and `L`. The five binders inside the
proposition occur in this order:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit |
| 2 | `L : Type u` | Explicit |
| 3 | `[Field K]` | Instance-implicit |
| 4 | `[Field L]` | Instance-implicit |
| 5 | `[Algebra K L]` | Instance-implicit |

The conclusion is equality in `Subgroup Kˣ`. The theorem preserves the
source's unrestricted field/algebra hypotheses. There is no
finite-dimensionality, finite-module, separability, Galois, local-field,
valuation, topology or other additional premise. Applying
`normClass_ker K L` obtains the subgroup equality, with the three
structures inferred as instances.

## Actual norm image and canonical quotient

The imported constructions are the published ones:

```lean
normUnits K L : Lˣ →* Kˣ
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

The norm runs from extension units to base-field units. Its image
subgroup consists of exactly the units `x : Kˣ` for which some
`y : Lˣ` satisfies `normUnits K L y = x`. The named quotient is
base-field units modulo this actual image. The canonical class map
is `QuotientGroup.mk' (localNormSubgroup K L)`, expressed through
`NormQuotient K L` with its published `normQuotientCommGroup K L`
structure. Its kernel consists of those units whose norm class is
the identity. The theorem identifies this kernel with the image
subgroup, without replacing any of these named constructions.

Mathlib defines `Algebra.norm K` as the determinant of multiplication
in `Mathlib/RingTheory/Norm/Defs.lean:59–62`. Its theorem
`Algebra.norm_eq_one_of_not_module_finite`, at lines 76–79, makes
the norm constantly `1` when the extension is not a finite module.
Then all unit norms are `1` and the image is the identity subgroup.
The result includes these algebras with Mathlib's convention.

## Implemented proof

The complete proof is:

```lean
by
  intro K L _ _ _
  let N := localNormSubgroup K L
  exact QuotientGroup.ker_mk' (N := N)
```

The first line introduces all five internal term binders, preserving
their order and kinds. The local abbreviation `N` names the actual
norm subgroup. Mathlib's `QuotientGroup.ker_mk'` states that the kernel
of the canonical quotient homomorphism is the subgroup being divided
out. The named `normClass` reduces to that homomorphism, and its named
quotient and group structure reduce to the canonical quotient and
structure. Thus the Mathlib result has the required type by
definitional equality. Normality is supplied by the commutative group
of field units, with no new hypothesis.

This is the original proof at source lines 195–197, preceded by the
introductions needed for the Library's closed target. The reused
generic theorem is in the approved
`Mathlib/GroupTheory/QuotientGroup/Defs.lean:142–143`; its proof is
`Subgroup.ext eq_one_iff`. No helper declaration is added.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:192–197`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L192-L197):
docstring at line 192, theorem telescope at line 193, subgroup equality
at line 194, and proof at lines 195–197. The complete original was
read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Its norm-subgroup, quotient and class-map definitions are at lines
26–54. The original unit norm is in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`, SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normClass_ker` | `normClass_ker : NormClassKerStatement.{u}` |
| Original theorem's telescope and conclusion | Existing closed `NormClassKerStatement.{u}` |
| `normUnits` | Existing `normUnits` |
| `localNormSubgroup` | Existing `localNormSubgroup` |
| `NormQuotient` | Existing `NormQuotient` |
| `normQuotientCommGroup` | Existing `normQuotientCommGroup` |
| `normClass` | Existing `normClass` |

Only the first row adds a declaration. Worker 107's modification on
1 November 2026 adds the namespace prefix, uses the published closed
target, introduces its five binders and retains the source proof.
The sole import is U020 Statements. The source's noncomputable
section, unused universe `v` and all other declarations are omitted.
M093 has no compatibility change in the feasibility patch10.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution material
is registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source-ID errata locations in the workspace, project and supplied
Library were checked; none exists.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Upstream used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and scope

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, released under Apache-2.0, author
Naganori Yamaguchi (assisted by OpenAI Codex). The Lean file includes
the dated modification record. Worker 107 extracted this proof from
the pinned original and wrote its companion; no worker draft was
reused. Published dependencies and their attribution remain unchanged.

The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained
unchanged in `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The NOTICE's ValuedFieldTheory list has no NormQuotient-specific
third-party entry; existing dependency notices are preserved.

This is the generic canonical-quotient kernel equality. M093.021 and
later units remain separate. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` still requires the named Artin
kernel and surjectivity, actual host quotient and evaluation, and
topology obligations. Independent semantic acceptance and Integrator
publication are separate from development compilation.
