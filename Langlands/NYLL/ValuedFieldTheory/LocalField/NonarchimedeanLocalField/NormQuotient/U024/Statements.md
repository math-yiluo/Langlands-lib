# Inclusion-induced norm quotient maps on representatives

This module defines the unproved statement interface
`Langlands.NYLL.LocalFieldTheory.NormQuotientMapOfLENormClassStatement.{u}`.
It asserts that the named homomorphism induced by an inclusion of actual
norm image subgroups takes the source class of a base-field unit to the
target class of the same unit. This is the statement phase of M093.024 in
the [NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

## Complete closed proposition

Inside namespace `Langlands.NYLL.LocalFieldTheory`, the entire definition is:

```lean
def NormQuotientMapOfLENormClassStatement : Prop :=
  ∀ (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L ≤ localNormSubgroup K M) (x : Kˣ),
    normQuotientMapOfLE K L M h (normClass K L x) = normClass K M x
```

The unapplied declaration has type `Prop`, with no external term or
instance parameters. Its sole universe parameter `u` is arbitrary and
shared by `K`, `L` and `M`. All ten original binders are quantified
inside the proposition, preserving this order and these binder kinds:

| Position | Binder | Kind and meaning |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit source extension-field type |
| 3 | `M : Type u` | Explicit target extension-field type |
| 4 | `[Field K]` | Instance-implicit field structure on `K` |
| 5 | `[Field L]` | Instance-implicit field structure on `L` |
| 6 | `[Field M]` | Instance-implicit field structure on `M` |
| 7 | `[Algebra K L]` | Instance-implicit specified algebra structure |
| 8 | `[Algebra K M]` | Instance-implicit specified algebra structure |
| 9 | `h : localNormSubgroup K L ≤ localNormSubgroup K M` | Explicit inclusion proof |
| 10 | `x : Kˣ` | Explicit representative in base-field units |

For `H : NormQuotientMapOfLENormClassStatement.{u}`, the expression
`H K L M h x` gives the displayed equation, with the five field and
algebra instances inferred. Both sides are elements of the actual named
`NormQuotient K M`.

The only premise beyond the three fields and two algebra structures is
the inclusion `h`. There is no `Algebra L M`, scalar tower,
finite-dimensionality, finite-module, separability, Galois, local-field,
valuation, topology, surjectivity or exact-kernel premise.

## Actual norm images, inclusion direction and representative equation

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U023.Definitions`.
It retains the published `M093.023.END` boundary and all 37 imported
Library modules and their Markdown companions unchanged. The existing
constructions have the following meaning:

```lean
normUnits K L : Lˣ →* Kˣ
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
normQuotientMapOfLE K L M h : NormQuotient K L →* NormQuotient K M
```

The corresponding norm constructions also apply with `M` in place of
`L`. The subgroup is the actual image: membership means that the
base-field unit is the norm of an extension-field unit. `normClass` is
the canonical quotient homomorphism, and the quotients carry their
published `normQuotientCommGroup` structures.

The hypothesis goes from the source image to the target image:
`localNormSubgroup K L ≤ localNormSubgroup K M`. Thus the source quotient
divides by a smaller subgroup and the target quotient divides by a larger
subgroup. The already defined `normQuotientMapOfLE` descends the target
projection `normClass K M` through the source quotient. The equation in
this proposition says precisely that applying that named map to
`normClass K L x` gives `normClass K M x`, using the same `x : Kˣ`.
No map from `L` to `M` is supplied.

The norm retains Mathlib's unrestricted `Algebra.norm K`, the determinant
of multiplication in `Mathlib/RingTheory/Norm/Defs.lean:59–62` at the
approved pin. It is the usual norm for finite-dimensional field
extensions. When the extension is not a finite module,
`Algebra.norm_eq_one_of_not_module_finite` at lines 76–79 makes it
constantly `1`. The unit norm is then constantly the unit `1` and its
image subgroup is trivial. This convention applies separately to `L/K`
and `M/K`; both remain quantified here, subject only to the displayed
inclusion. No finite-dimensionality premise has been added.

## Pinned original and adaptation

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:222–229`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L222-L229):
the docstring is line 222, the simp attribute is line 223, the theorem
name, telescope and result are lines 224–228, and its proof is line 229.
The complete original file was read and has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Its norm subgroup, quotient and canonical projection are at lines 26–54;
the inclusion-induced map is at lines 213–220. The original unit norm is
in `Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`, SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normQuotientMapOfLE_normClass` (theorem telescope and result) | `NormQuotientMapOfLENormClassStatement` (closed Prop definition) |
| `normQuotientMapOfLE` | Existing `normQuotientMapOfLE` in U023.Definitions |
| `normUnits` | Existing `normUnits` |
| `localNormSubgroup` | Existing `localNormSubgroup` |
| `NormQuotient` | Existing `NormQuotient` |
| `normQuotientCommGroup` | Existing `normQuotientCommGroup` |
| `normClass` | Existing `normClass` |

Only the first row introduces a declaration. Worker 107's modification
on 1 November 2026 adds the namespace prefix, moves the original ten
binders inside a closed `Prop` definition, and uses the sole published
U023 Definitions import. The binder order and kinds, shared universe,
equation and original docstring are retained. The original proof and
simp attribute, noncomputable section, unused universe `v` and all other
declarations are omitted. M093 has no feasibility patch10 change.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source-ID errata paths in the workspace, project and supplied Library
were checked; none exists. Exact-name TaskHub and Lean searches found
only this assigned task and no competing declaration. No shared draft
was reused.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Statement boundary and attribution

This is an unproved statement interface. It supplies a proposition,
with no proof of that proposition or simp registration.
The exact theorem name
`Langlands.NYLL.LocalFieldTheory.normQuotientMapOfLE_normClass`
is reserved for a separate proof task after this target is independently
accepted and published. M093.025, later source units and host adapters
remain outside this unit. Compilation and declaration inspection do not
replace independent semantic acceptance or Integrator publication.

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, and the Lean file contains the explicit dated modification
record. Worker 107 extracted this statement directly from the pinned
original and wrote this companion. There are no other project coauthors
or reused-draft contributors to this unit. Published dependency authors
and attribution remain unchanged.

The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
unchanged through `repository_paths`, with respective SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
They match the retained originals. The NOTICE's ValuedFieldTheory table
has no NormQuotient-specific third-party entry; all inherited dependency
notices are preserved.

This generic representative equation supplies no host named Artin map,
norm-kernel theorem, quotient equivalence, host evaluation, continuity
or reciprocity proof. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open with its named-family,
every-prime, arbitrary supplied topology and actual norm-image
requirements. The existing cohomological definitions and proof targets
retain their meaning.
