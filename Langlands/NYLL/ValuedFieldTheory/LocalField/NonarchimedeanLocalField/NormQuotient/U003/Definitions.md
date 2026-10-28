# Group structure on the general norm quotient

`Langlands.NYLL.LocalFieldTheory.normQuotientCommGroup` is the commutative
group structure on the published general norm quotient
`Langlands.NYLL.LocalFieldTheory.NormQuotient K L`. Its complete
declaration telescope is

```lean
(K L : Type u) [Field K] [Field L] [Algebra K L] :
    CommGroup (Langlands.NYLL.LocalFieldTheory.NormQuotient K L)
```

Here `u` is arbitrary and shared by the two fields. The declaration is a
global `instance` with default priority, so typeclass inference supplies it
for `NormQuotient K L` whenever these four hypotheses are available.

Mathematically, `NormQuotient K L` is `Kˣ ⧸ N`, where `N` is the published
norm image subgroup `Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L`.
That subgroup is the range of `Units.map (Algebra.norm K)` on `Lˣ`. Since
`Kˣ` is commutative, every subgroup is normal and the cosets of `N` form an
abelian group. Two cosets are multiplied by multiplying representatives. The
identity is the class of `1`, and the inverse of a class is the class of the
inverse representative.

The instance contributes no new group law. It is, definitionally, Mathlib's
standard structure `QuotientGroup.Quotient.commGroup N`, from
`Mathlib/GroupTheory/QuotientGroup/Defs.lean` lines 151–154. That instance
provides a commutative group on `G ⧸ N` for every subgroup `N` of a
commutative group `G`, without a separate normality hypothesis. It extends
Mathlib's quotient group `QuotientGroup.Quotient.group` by commutativity.
Here `G = Kˣ` carries Mathlib's commutative group of units of the field `K`.

There is no finite-dimensional, separable, Galois, local-field, valuation,
or topology hypothesis. As in the published quotient, the norm is Mathlib's
general `Algebra.norm`, which is constantly `1` when `L` is not a finite
`K`-module (`Algebra.norm_eq_one_of_not_module_finite`). In that case `N` is
the trivial subgroup `⊥`, as the private check below verifies, so the
quotient is a copy of `Kˣ`.

## Original and adapted declaration

This extraction is M093.003 of the accepted NYLL declaration partition.
Its original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, in
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Lines 1–5 contain the attribution and line 24 declares the source universes
`u v`. Lines 26–28 contain `localNormSubgroup` and lines 30–32 contain
`NormQuotient`. Lines 34–38 contain this instance. The original file has
SHA-256 `26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The complete original file was read.

The retained original is in the `n-yamaguchi-0729--ClassFieldTheory/source/`
directory of registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The related attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The published partition records no patch10 modification to this module.
The project, workspace and current Library errata locations contain no
applicable erratum for either registered source.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientCommGroup` | `Langlands.NYLL.LocalFieldTheory.normQuotientCommGroup` |

The namespace prefix changes. The source parameters, result type, instance
attribute, docstring and two-step tactic body are preserved:

```lean
  change CommGroup (Kˣ ⧸ localNormSubgroup K L)
  infer_instance
```

The `change` step exposes the published quotient definition; it is accepted
because `NormQuotient K L` unfolds to `Kˣ ⧸ localNormSubgroup K L`. The
`infer_instance` step then finds Mathlib's instance on the concrete quotient.
Inside the namespace, `NormQuotient` and `localNormSubgroup` resolve to the
published M093.002 and M093.001 adaptations of source lines 31 and 27.
The unused universe `v` is omitted. The source's `noncomputable section` is
retained.

## Imports and dependency pruning

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U002.Definitions`,
which supplies `NormQuotient`. The current Library's corresponding Lean and
Markdown were checked before reuse. That module imports only the published
M093.001 module `NormQuotient.U001.Definitions`. In turn, that imports only
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
whose sole import is `Mathlib.RingTheory.Norm.Transitivity`. No other NYLL
or Library module is in the import closure.

No extra import is needed for the group instance. A scan of Mathlib's import
headers finds `Mathlib.GroupTheory.QuotientGroup.Defs`, which declares
`QuotientGroup.Quotient.commGroup`, in the transitive import closure of
`Mathlib.RingTheory.Norm.Transitivity`. The successful build below confirms
this. As in M093.002, the source module's direct imports of
`Mathlib.Data.Finset.Basic`, `Mathlib.GroupTheory.QuotientGroup.Basic`,
`Mathlib.LinearAlgebra.FiniteDimensional.Basic` and
`Mathlib.RingTheory.Norm.Basic` are not repeated. The same header scan finds
them transitively in the reduced closure.

The partition's dependency `M093.002.END` is met by the published quotient
definition. The instance needs none of M092's evaluation, negation or tower
results and no later M093 declaration.

## Machine checks

A Lean-service build and declaration inspection succeeded with Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, without errors or
warnings. Inspection reports a definition with the single universe parameter
`u`. It lists only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`, inherited from the Mathlib declarations it uses; no new axiom
occurs.

A separate private check also succeeded without errors or warnings. It
verified the following.

- The unapplied constant has exactly the telescope above and is registered
  as an instance.
- Without opening any namespace, inference for
  `CommGroup (Langlands.NYLL.LocalFieldTheory.NormQuotient K L)` succeeds
  under exactly the four source hypotheses. It returns
  `normQuotientCommGroup K L`. The `Group`, `Mul`, `One` and `Inv`
  structures inferred on `NormQuotient K L` are, already at
  reducible-and-instances transparency, the corresponding projections of
  this instance.
- With explicit printing, the elaborated body is
  `@id (CommGroup (NormQuotient K L)) (@inferInstance _ (QuotientGroup.Quotient.commGroup (localNormSubgroup K L)))`.
  The outer `id` is the type hint that `change` inserts.
- At Lean's default transparency, reflexivity proves that the instance
  equals `QuotientGroup.Quotient.commGroup (localNormSubgroup K L)`. It
  likewise proves that its underlying group equals
  `QuotientGroup.Quotient.group (localNormSubgroup K L)`. Reflexivity also
  equates the inferred instance with the one inferred for
  `Kˣ ⧸ (Units.map (Algebra.norm K)).range`.
- Reflexivity proves that the product of the classes of `x` and `y` is the
  class of `x * y`. The identity is the class of `1`, and the inverse of
  the class of `x` is the class of `x⁻¹`.
- If `L` is not a finite `K`-module, `localNormSubgroup K L = ⊥`.

At reducible-and-instances transparency, the comparison with Mathlib's
instance fails, as recorded with `fail_if_success`. The two sides have the
types `CommGroup (NormQuotient K L)` and `CommGroup (Kˣ ⧸ localNormSubgroup K L)`,
and the published `NormQuotient` is an ordinary definition, not reducible.
At that transparency the instance does equal the body displayed above, with
the `id` hint. This matches the source, which keeps `NormQuotient` a
separate definition; inference for `CommGroup (NormQuotient K L)` returns
this named instance, while inference on the concrete quotient returns
Mathlib's instance. The comparison between the two is therefore at default
transparency.

Together these checks verify the reduced import closure, the preserved
declaration and its typeclass behavior. They do not constitute independent
semantic acceptance.

## Host comparison and scope

The existing `Langlands.LocalClassField.NormQuotient` in
`Langlands/ClassFieldTheory/Local/Norms.lean` is an `abbrev` with independent
field universes `u` and `v` and a `[FiniteDimensional K L]` premise. Its group
structure is not a named declaration: the private check confirmed that
inference finds `QuotientGroup.Quotient.commGroup` on the host
`normSubgroup K L` through the `abbrev`. The full telescopes differ.

The private check verified one specialization by default-transparency
reflexivity. With a shared universe, aligned field and algebra instances, and
`[FiniteDimensional K L]`, `normQuotientCommGroup K L` equals the
`CommGroup` instance inferred for the host `NormQuotient K L`. The host
definitions and instances are unchanged, and no comparison theorem is part of
this unit.

The instance supplies only the commutative group structure on the general
norm quotient. It makes no assertion about an Artin map, reciprocity, a norm
kernel, finiteness, openness, a quotient topology or continuity. The concrete
equivalence `normQuotientConcreteEquiv` (M093.004), `normClass` (M093.005),
lifts, other equivalences, theorem statements and proofs belong to later
units.

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

Worker 248 extracted and documented M093.003 on 28 October 2026, added
the namespace prefix, replaced the source imports with the published
`NormQuotient` module, and omitted the unused universe and all other source
declarations. The source telescope, docstring and instance body were
retained. No other worker's draft or patch10 implementation was reused.
