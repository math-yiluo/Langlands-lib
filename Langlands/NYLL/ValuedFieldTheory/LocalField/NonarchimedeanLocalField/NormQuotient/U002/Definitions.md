# General norm quotient

`Langlands.NYLL.LocalFieldTheory.NormQuotient` defines the type of
base-field units modulo norms of extension-field units. Its complete
declaration telescope is

```lean
(K L : Type u) [Field K] [Field L] [Algebra K L] : Type u
```

Here `u` is arbitrary and shared by the two fields. The body is exactly
`Kˣ ⧸ Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L`, using the
published norm image subgroup. That subgroup is
`(Langlands.NYLL.LocalFieldTheory.normUnits K L).range`, and `normUnits` is
`Units.map (Algebra.norm K)`. The notation `⧸` is Mathlib's
`QuotientGroup.instHasQuotientSubgroup` from
`Mathlib/GroupTheory/Coset/Defs.lean`: the quotient of `Kˣ` by the left-coset
relation `QuotientGroup.leftRel` of the subgroup.

There is no finite-dimensional, separable, Galois, local-field, valuation,
or topology hypothesis. The term uses Mathlib's general algebra norm,
including its convention for algebras that are not finite modules.

This unit defines only the quotient type. Its commutative group instance
is the separate later unit M093.003, so no group, topology or other
structure on `NormQuotient K L` is declared here.

## Original and adapted declaration

This extraction is M093.002 of the accepted NYLL declaration partition.
Its original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, in
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Lines 1–5 contain the attribution, line 24 declares the source universes
`u v`, lines 26–28 contain the prerequisite `localNormSubgroup`, and lines
30–32 contain this definition. The original file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The complete original file was read.

The retained original is in the `n-yamaguchi-0729--ClassFieldTheory/source/`
directory of registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The related attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The published partition records no patch10 modification to this module.
The project and current Library errata locations contain no applicable
erratum for either registered source.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.NormQuotient` | `Langlands.NYLL.LocalFieldTheory.NormQuotient` |

The namespace prefix changes; the source parameters, result type, body and
docstring are preserved. The body's reference to `localNormSubgroup`
resolves inside the namespace to the published
`Langlands.NYLL.LocalFieldTheory.localNormSubgroup`, the M093.001 adaptation
of the source's line 27 declaration. The unused universe `v` is omitted.
The source's `noncomputable section` is retained.

## Imports and dependency pruning

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions`,
which supplies `localNormSubgroup`. The current Library's corresponding
Lean and Markdown were checked before reuse. That module imports only
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
which in turn imports only `Mathlib.RingTheory.Norm.Transitivity`. No other
NYLL or Library module is in the import closure.

No extra import is needed for the quotient type. Mathlib's
`Mathlib/GroupTheory/Coset/Defs.lean`, which defines `QuotientGroup.leftRel`
and `QuotientGroup.instHasQuotientSubgroup`, is already in the transitive
import closure of `Mathlib.RingTheory.Norm.Transitivity`. This was found by
a scan of Mathlib's import headers and is confirmed by the successful build
below. The source module's further direct imports of
`Mathlib.Data.Finset.Basic`, `Mathlib.GroupTheory.QuotientGroup.Basic`,
`Mathlib.LinearAlgebra.FiniteDimensional.Basic` and
`Mathlib.RingTheory.Norm.Basic` are therefore omitted here. This pruning
concerns the direct imports and required NYLL declarations. The same header
scan finds all four Mathlib modules transitively in the reduced closure.

The partition's dependency `M093.001.END` is met by the published
subgroup definition. This definition needs none of M092's evaluation,
negation or tower results and no later M093 declaration.

A Lean-service build and declaration inspection succeeded with Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, without errors or
warnings. Inspection reports a definition with the single universe parameter
`u`. It lists only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`, inherited from the Mathlib declarations it uses; no new axiom
occurs.

A separate private check also succeeded without errors or warnings. It
printed the full unapplied type, assigned the unapplied constant to exactly
the telescope above, and verified three bodies by reflexivity:
`Kˣ ⧸ localNormSubgroup K L`, `Kˣ ⧸ (normUnits K L).range` and
`Kˣ ⧸ (Units.map (Algebra.norm K)).range`.

Together these checks verify the reduced import closure and the preserved
declaration. They do not constitute independent semantic acceptance.

## Host comparison and scope

The existing `Langlands.LocalClassField.NormQuotient` in
`Langlands/ClassFieldTheory/Local/Norms.lean` is an `abbrev` with independent
field universes `u` and `v` and a `[FiniteDimensional K L]` premise. Its
body is `Kˣ ⧸ Langlands.LocalClassField.normSubgroup K L`, where the host
`normSubgroup` is `(Units.map (Algebra.norm K)).range`. It is not a
telescope-preserving alias of the general declaration here.

Under finite specialization in a shared universe with aligned field and
algebra instances, both quotients are by the same actual norm range. The
private check above also verified, by reflexivity, that in this
specialization `localNormSubgroup K L` equals the host `normSubgroup K L`
and `NormQuotient K L` equals the host `NormQuotient K L`. Both
reflexivity checks used Lean's default transparency. The host definitions
are unchanged, and no comparison theorem is part of this unit.

The general declaration here is not narrowed to the host's
finite-dimensional or p-adic setting. It defines the quotient type only and
makes no assertion about an Artin map, reciprocity, a norm kernel,
finiteness, openness, a quotient topology or continuity. The group
instance, concrete equivalences, `normClass`, lifts, evaluation statements
and proofs belong to later units.

## Attribution and changes

The original copyright and author header is retained verbatim, including
Naganori Yamaguchi's 2026 copyright and the author credit
“Naganori Yamaguchi (assisted by OpenAI Codex)”. The source is Apache-2.0.
Its unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain included through
the submission's `repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Both are byte-identical to the retained source snapshot. The original
NOTICE does not list `NormQuotient.lean`.

Worker 248 extracted and documented M093.002 on 27 October 2026, added
the namespace prefix, replaced the source imports with the published
`localNormSubgroup` module, and omitted the unused universe and all other
source declarations. The source telescope, docstring and body were
retained. No other worker's draft or patch10 implementation was reused.
