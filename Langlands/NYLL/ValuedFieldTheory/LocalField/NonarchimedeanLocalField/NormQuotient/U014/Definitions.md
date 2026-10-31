# First isomorphism theorem for the actual norm quotient

This module defines
`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSurjective`,
the canonical multiplicative equivalence from the actual norm quotient
to the target of a supplied surjective homomorphism with that norm
subgroup as its kernel. It is data unit M093.014 in the
[NYLL declaration partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

## Complete interface

Inside `namespace Langlands.NYLL.LocalFieldTheory`, its complete
unapplied telescope and result are:

```lean
normQuotientEquivOfSurjective.{u,v}
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) : NormQuotient K L ≃* M
```

The universes `u` and `v` are independent and arbitrary. The fields
`K` and `L` share `u`, while the target group `M` lives in `v`.
All three type parameters are implicit. The two field structures,
algebra structure and group structure are instance-implicit; `f`, `hf`
and `hker` are explicit, in that order. There are ten binders in total.
The hypothesis `hker` is equality in the displayed orientation,
from `f.ker` to `localNormSubgroup K L`. The target requires only
`Group M`; no commutativity instance on `M` is assumed.
The result is a multiplicative equivalence, so this is a data
definition rather than a proposition.

The definition adds no finite-dimensionality, separability, Galois,
local-field, valuation or topological hypothesis. All mathematical
inputs are the displayed field and algebra structures, group, map,
surjectivity proof and exact kernel equality.

## Actual norm image and quotient

The unchanged published dependencies define

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
```

Thus the source is the quotient of the base-field unit group by the
actual range of the unit norm `Lˣ →* Kˣ`. Its multiplication is the
usual quotient multiplication supplied by the published
`normQuotientCommGroup` instance. The kernel premise identifies this
specific image subgroup with the kernel of the supplied map `f`.

`Algebra.norm K` is Mathlib's unrestricted determinant norm: the
determinant of the endomorphism given by left multiplication.
The approved `Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62,
defines it without a finite-module premise. Its
`Algebra.norm_eq_one_of_not_module_finite`, lines 76–79, states that
when `L` is not a finite `K`-module, this norm is constantly `1`.
In that case the unit norm is constantly the unit `1`, its range is
the trivial subgroup and the source is the quotient by that subgroup.
The supplied `hker` then requires a trivial kernel. The constructor
retains this convention and does not add finiteness to its interface.

## Canonical composition and noncomputability

The implementation preserves the original body:

```lean
  change (Kˣ ⧸ localNormSubgroup K L) ≃* M
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
```

The `change` step exposes the concrete quotient and its
definitionally matching group structure. Since `hker.symm` has type
`localNormSubgroup K L = f.ker`, the first factor is

```lean
Kˣ ⧸ localNormSubgroup K L ≃* Kˣ ⧸ f.ker
```

It transports the quotient along subgroup equality. Its underlying
maps preserve representatives, using `Subgroup.quotientEquivOfEq`.
Normality of the norm subgroup is inferred because `Kˣ` is
commutative; the kernel is also normal. No additional normality
argument is required.

The second factor is Mathlib's canonical first-isomorphism equivalence
`Kˣ ⧸ f.ker ≃* M`, obtained from `f` and `hf`. The approved
`Mathlib/GroupTheory/QuotientGroup/Basic.lean`, lines 134–159,
constructs it through `quotientKerEquivOfRightInverse`.
Surjectivity supplies the existence of a right inverse; the
implementation uses `hf.hasRightInverse.choose_spec` to choose one
classically. Its inverse sends `y : M` to the quotient class of the
chosen preimage. Any two preimages differ by the kernel, so their
classes agree. The forward map is the kernel lift of `f`, and
composing the two factors gives the canonical first-isomorphism
equivalence for the named norm quotient. This chosen inverse explains
the retained `noncomputable section`.

`quotientMulEquivOfEq` is defined at lines 162–168 of the same
Mathlib file. The implementation imports this existing machinery
through the published dependency chain. The separate M093.015 unit
reserves the representative equation, its published `Prop` target,
exact proof and simp registration. This candidate adds only the data
definition.

## Original source and adaptation

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 137–144: the docstring is at 137, declaration and telescope at
138–141, and body at 142–144. The whole file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Lines 1–180 were read for this extraction, including the underlying
norm-image/quotient definitions, predecessor and separately reserved
representative theorem at 146–158.

The source is retained in registration
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Registration `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
retains additional attribution material. The source-ID errata
locations in the workspace, project and current Library were checked;
no applicable erratum was found.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientEquivOfSurjective` | `Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSurjective` |

The namespace prefix is the only change to the declaration. Both
independent universes, the complete telescope, binder kinds,
hypothesis orientation, result, docstring and body are preserved.
The source imports are replaced by the sole direct import
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U013.Proofs`.
This preserves `M093.013.END` and supplies the original definitions
under `Langlands.NYLL` with the required Mathlib quotient API.
All 19 imported Library modules and their same-stem Markdown
companions are unchanged. The partition records no patch10 change
to the original module.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 with
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The generic first-isomorphism interface used here agrees at the
approved pin. Compilation, independent semantic review and
Integrator publication remain distinct evidence.

## Attribution and scope

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi
(assisted by OpenAI Codex)”, released under Apache-2.0.
A dated modification record identifies Worker 107's extraction,
namespacing and import changes on 31 October 2026. Worker 107
extracted this unit directly from the pinned original and wrote its
companion. No other project worker supplied code or a reused draft.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
in `repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the retained originals. The inherited NOTICE's
ValuedFieldTheory included-source list has no NormQuotient-specific
third-party entry. Existing dependency notices and attribution
remain preserved.

This conditional algebraic constructor supplies no named Artin map,
norm-kernel or surjectivity theorem for such a map, host quotient or
evaluation adapter, or topology theorem. Parent finite reciprocity
task `1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open.
