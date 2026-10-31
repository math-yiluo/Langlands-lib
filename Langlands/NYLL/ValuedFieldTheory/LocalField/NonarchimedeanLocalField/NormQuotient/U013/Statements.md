# Equal norm subgroups identify classes of the same representative

This module specifies the representative equation for the published
`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfNormSubgroupEq`.
It is the statement phase of M093.013 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
The proposition is defined here; its proof is a separate obligation.

## Closed interface

Inside `Langlands.NYLL.LocalFieldTheory`, the complete declaration is:

```lean
def NormQuotientEquivOfNormSubgroupEqNormClassStatement.{u} : Prop :=
  ∀ (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) (x : Kˣ),
    normQuotientEquivOfNormSubgroupEq K L M h (normClass K L x) =
      normClass K M x
```

The complete unapplied declaration has type `Prop`: it has no term
parameters outside its body. Its only universe parameter is the arbitrary
`u`, shared by the three fields; it is not restricted to `Type 0`.
All ten source term binders occur inside the proposition, in source order:
the three explicit fields `K`, `L`, `M`; the three instance-implicit field
structures; the two instance-implicit algebra structures `Algebra K L`
and `Algebra K M`; the explicit equality `h`; and the explicit unit `x`.

The equality hypothesis concerns subgroups of the common group `Kˣ`.
There is no algebra structure from `L` to `M`. No finite-module,
finite-dimensionality, separability, Galois, local-field, valuation,
topology, normality, surjectivity or kernel premise is added. These
are exactly the original theorem's hypotheses, even though its source
module is placed under nonarchimedean local fields.

## Norm images and quotient representatives

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U012.Definitions`.
Its unchanged published dependencies supply the following definitions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

The corresponding definitions with `M` in place of `L` use the other
supplied algebra structure. Thus `h` identifies the actual ranges of the
unit norm maps `Lˣ →* Kˣ` and `Mˣ →* Kˣ`. The subgroups are neither
arbitrary comparison data nor assumed norm kernels.

The published U012 equivalence has type
`NormQuotient K L ≃* NormQuotient K M`. It uses
`QuotientGroup.quotientMulEquivOfEq h` after exposing those two concrete
quotients. Their usual group structures are supplied by the published
`normQuotientCommGroup` instances. Since `Kˣ` is commutative, the
subgroups are normal without any extra hypothesis.

The source `normClass K L x` is the coset of `x` modulo the norm image
from `L`. The target `normClass K M x` is the coset of that same `x`
modulo the norm image from `M`. Both sides of the asserted equation live
in `NormQuotient K M`. The left side coerces the named U012
multiplicative equivalence to a function and applies it to the named
source class; the right side uses the named target class map. All of
these constructions are imported, with no replacements or new instances.

The norm convention is the unrestricted Mathlib `Algebra.norm K`.
In the approved `Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define
it as the determinant of multiplication without a finite-module premise.
Lines 76–79 prove `Algebra.norm_eq_one_of_not_module_finite`: if the
algebra is not a finite module, this norm is constantly `1`. Its
restriction to units then has trivial image. This convention applies
separately to `L/K` and `M/K`. If both are nonfinite modules, both norm
images are trivial; if just one is nonfinite, `h` requires the other
norm image to be trivial too. The proposition retains these cases.

## Original passage and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
pinned at `fbd320cd8b1b06487c58227e92eb135794267709`.
The selected passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 124–135](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L124-L135).
The docstring is at 124–125, the `simp` attribute at 126, the theorem
telescope and equation at 127–132, and the proof at 133–135.
The whole file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Lines 1–180 were read for this extraction, including the definitions
of the actual norm subgroup, quotient and class map and the immediately
preceding U012 equivalence at 115–122.

| Original declaration | Adapted declaration used here |
| --- | --- |
| `LocalFieldTheory.normQuotientEquivOfNormSubgroupEq_normClass` | `Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfNormSubgroupEqNormClassStatement` |
| `LocalFieldTheory.normQuotientEquivOfNormSubgroupEq` | `Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfNormSubgroupEq` |
| `LocalFieldTheory.normClass` | `Langlands.NYLL.LocalFieldTheory.normClass` |
| `LocalFieldTheory.NormQuotient` | `Langlands.NYLL.LocalFieldTheory.NormQuotient` |
| `LocalFieldTheory.localNormSubgroup` | `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` |
| `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits` |

Only the first row introduces a declaration in this module; the other
rows name unchanged published dependencies. The theorem's telescope
moves inside a closed `Prop` definition with its order, explicitness,
instance binders and shared universe preserved. The equation is
unchanged. The namespace gains `Langlands.NYLL`. The duplicate sentence
in the original docstring is removed. The unused source universe `v`,
the source-wide imports, the noncomputable section and all other
declarations are omitted. A proposition definition needs no
noncomputable section. The only import becomes the public U012
Definitions module, following `M093.012.END`. The partition records
no patch10 modification of the source module.

The original is retained in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Source-ID errata locations in the workspace, project and current Library
were checked; no applicable erratum was found.

Fresh TaskHub and exact-name Lean searches in the current Library,
workspace, staging, shared drafts and approved Mathlib found no duplicate
statement or proof task. The two old upstream copies in the source-audit
shared draft were not reused. Mathlib already supplies the generic
quotient calculation: `Mathlib/GroupTheory/QuotientGroup/Basic.lean`,
lines 162–173 define the equality-induced equivalence and prove
`QuotientGroup.quotientMulEquivOfEq_mk`. This statement preserves the
source-specific named norm-quotient interface.

## Statement and proof boundary

This file contains only the proposition definition. It omits the source
proof and `@[simp]` attribute. The source proof exposes the concrete
quotient equation with `change` and applies the existing Mathlib
`QuotientGroup.quotientMulEquivOfEq_mk`; that description records the
source route, not a proof included in this unit. The theorem name
`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfNormSubgroupEq_normClass`
is reserved for a separate exact proof task after this target is
independently accepted and published. M093.014 and later units remain
separate and depend on the required earlier publications.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`;
it differs from upstream's Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Compilation and inspection
check the proposition's declaration shape; independent semantic review
and publication are separate requirements.

This generic algebraic equation supplies no named Artin family,
norm-kernel theorem, host quotient or evaluation adapter, topology or
continuity proof. Parent task `1cbd1968-d285-4b34-822c-f6b5599d1c38`
retains those obligations and remains open.

## Attribution

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. A dated modification
record identifies Worker 107's extraction and changes. Worker 107
performed this adaptation directly from the pinned original and authored
this companion; no other project worker supplied code or a reused draft.
All 17 imported Library modules and their Markdown companions remain
unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
in `repository_paths`. Their SHA-256 hashes are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the originals. The inherited NOTICE and the supplement's
ValuedFieldTheory included-source table have no NormQuotient-specific
third-party entry. Existing dependency notices and attribution are
preserved.
