# Norm quotient map induced by norm subgroup inclusion

This module defines
`Langlands.NYLL.LocalFieldTheory.normQuotientMapOfLE.{u}`.
It descends the identity on base-field units from the quotient by one
actual norm image to the quotient by a containing norm image.
This is the data definition M093.023 in the
[NYLL declaration partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

## Complete interface

Inside namespace `Langlands.NYLL.LocalFieldTheory`, the full telescope
and result are:

```lean
normQuotientMapOfLE.{u}
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L ≤ localNormSubgroup K M) :
    NormQuotient K L →* NormQuotient K M
```

The sole universe parameter `u` is arbitrary and shared by all three
fields. The nine term binders have exactly this order and these kinds:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit first extension-field type |
| 3 | `M : Type u` | Explicit second extension-field type |
| 4 | `[Field K]` | Instance implicit |
| 5 | `[Field L]` | Instance implicit |
| 6 | `[Field M]` | Instance implicit |
| 7 | `[Algebra K L]` | Instance implicit |
| 8 | `[Algebra K M]` | Instance implicit |
| 9 | `h : localNormSubgroup K L ≤ localNormSubgroup K M` | Explicit inclusion proof |

The result is a multiplicative homomorphism, so this is a data definition.
The only premise beyond the three fields and two specified algebra
structures is `h`. There is no `Algebra L M`, scalar-tower,
finite-dimensionality, separability, Galois, local-field, valuation,
topology, surjectivity or exact-kernel premise.

## Actual norm images and inclusion direction

The unchanged published dependencies define:

```lean
normUnits K L : Lˣ →* Kˣ
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

The same definitions apply with `M` in place of `L`. Thus `h` is an
inclusion of actual image subgroups in the common group `Kˣ`:
every norm of an `L`-unit is a norm of an `M`-unit. The source quotient
divides by the smaller subgroup, and the target quotient divides by the
larger subgroup. No map between `L` and `M` is supplied or needed.
The published `normQuotientCommGroup` instances give both quotients
their usual coset multiplication.

The norm is Mathlib's general `Algebra.norm K`, defined as the
determinant of left multiplication in
`Mathlib/RingTheory/Norm/Defs.lean:59–62` at the approved pin.
It is defined without a finite-module premise. In the finite-dimensional
field case it is the usual field norm. More generally, Mathlib uses the
constant value `1` when no finite basis exists; in particular,
`Algebra.norm_eq_one_of_not_module_finite` at lines 76–79 proves that
the norm is constantly `1` when the algebra is not a finite module.
Its restriction to units is then constantly the unit `1`, with trivial
image subgroup. These conventions apply separately to `L/K` and `M/K`.
If `L` is nonfinite over `K`, its trivial image is contained in every
target norm image. If `M` is nonfinite over `K`, `h` requires the
source image to be trivial too. The construction retains all these
algebras and uses the supplied inclusion in each case.

## Implemented quotient descent

The complete definition body is unchanged from the original:

```lean
  normQuotientLift (normClass K M) fun x hx =>
    (normClass_eq_one_iff_mem K M x).2 (h hx)
```

The published `normQuotientLift` accepts a homomorphism on `Kˣ`
and a proof that `localNormSubgroup K L` lies in its kernel. Here that
homomorphism is the canonical target projection `normClass K M`.
For `x : Kˣ` and `hx : x ∈ localNormSubgroup K L`, the inclusion
gives `h hx : x ∈ localNormSubgroup K M`. The published criterion
`normClass_eq_one_iff_mem K M x` turns this membership into
`normClass K M x = 1`. This is definitionally membership in the
kernel of `normClass K M`, so it supplies exactly the required
kernel-containment proof.

The lift's implicit fields are instantiated with `K` and `L`, and its
codomain with `NormQuotient K M`. The lift is the published wrapper
around `QuotientGroup.lift`; its multiplication and identity laws are
inherited from that construction. This descends the identity on the
common representative group through the two quotient projections,
without choosing representatives or changing either norm subgroup.
Mathlib's generic `QuotientGroup.map`
(`Mathlib/GroupTheory/QuotientGroup/Defs.lean:309–323`) provides the
general subgroup-preserving quotient-map construction. This unit
retains the source's norm-specific descent using its published lift
and norm-class criterion.

The source's `noncomputable section` is retained. The Lean file adds
only this definition. The formal representative-evaluation target
and proof belong to the separate M093.024 unit; this candidate adds
no evaluation theorem, instance or simp registration.

## Pinned source and adaptation

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:213–221`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L213-L221):
the docstring is line 213, the declaration, telescope and result are
lines 214–218, and the body is lines 219–220. Line 221 is blank.
The entire original file was read and has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The preceding norm-class criterion is at lines 206–211; the separately
reserved evaluation theorem is at lines 223–229.
The original unit norm is in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`, SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normQuotientMapOfLE` | `normQuotientMapOfLE` |
| `normQuotientLift` | Existing `normQuotientLift` in U007.Definitions |
| `normClass_eq_one_iff_mem` | Existing `normClass_eq_one_iff_mem` in U022.Proofs |
| `normUnits` | Existing `normUnits` |
| `localNormSubgroup` | Existing `localNormSubgroup` |
| `NormQuotient` | Existing `NormQuotient` |
| `normQuotientCommGroup` | Existing `normQuotientCommGroup` |
| `normClass` | Existing `normClass` |

Only the first row introduces a declaration. Worker 107's modification
on 1 November 2026 adds the namespace prefix, replaces the original
imports with the sole direct import
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U022.Proofs`,
and omits the unused universe `v` and all other declarations.
The telescope, result, docstring and body are preserved verbatim,
as is the noncomputable section. This import preserves the partition's
`M093.022.END` dependency. All 36 imported Library modules and their
Markdown companions remain unchanged. M093 has no feasibility
patch10 change.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source-ID errata locations in the workspace, project and supplied
Library were checked; none exists.

Fresh TaskHub and exact-name Lean searches found no competing task or
published definition. Older shared-draft matches are upstream copies
from the source audit; none was reused. Worker 107 extracted this
definition directly from the pinned original and wrote this companion.
There are no other project coauthors of this unit.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and scope

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, and the Lean file includes the dated modification record.
The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
unchanged in `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the retained originals. The original NOTICE and supplement's
ValuedFieldTheory table have no NormQuotient-specific third-party
entry. All inherited dependency attribution is preserved.

This generic inclusion-induced homomorphism supplies no host named
Artin map, host norm-kernel theorem, host quotient equivalence,
evaluation theorem or topology result. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open with all its
finite reciprocity requirements. M093.024, later source units and
host adapters remain separate. Development compilation is separate
from independent semantic acceptance and Integrator publication.
