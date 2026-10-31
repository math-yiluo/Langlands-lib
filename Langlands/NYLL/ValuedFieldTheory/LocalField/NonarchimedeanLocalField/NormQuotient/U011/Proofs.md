# The subgroup-equality norm-quotient equivalence on representatives

`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSubgroupEq_normClass.{u}`
proves exactly the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfSubgroupEqNormClassStatement.{u}`.
The theorem's declared type is that statement constant itself, at the
universe parameter `u`. The theorem has no external term parameters. The
proposition contains all eight binders:

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
  (N : Subgroup Kˣ) (h : Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L = N) (x : Kˣ),
  Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSubgroupEq K L N h
      (Langlands.NYLL.LocalFieldTheory.normClass K L x) =
    (QuotientGroup.mk x : Kˣ ⧸ N)
```

In words: let `N` be a subgroup of `Kˣ` that equals the norm subgroup.
Then the published equivalence
`normQuotientEquivOfSubgroupEq K L N h : NormQuotient K L ≃* Kˣ ⧸ N`
sends the norm class of any unit `x : Kˣ` to the class of the same unit
`x` modulo `N`. The equivalence keeps representatives.

## Universes and binders

There is one universe, `u`. It is arbitrary, and the two fields `K` and
`L` share it. The statement keeps the source binder kinds: `K` and `L` are
explicit; `Field K`, `Field L` and `Algebra K L` are instance-implicit;
the subgroup `N`, the equality `h` and the unit `x` are explicit.

There is one hypothesis, `h : localNormSubgroup K L = N`. There is no
premise that `N` is normal. `Kˣ` is commutative, so every subgroup of it
is normal, and Lean infers this by instance search. The theorem adds no
finite-dimensionality, separability, Galois, local-field, valuation,
topology, surjectivity or exact-kernel premise.

## Meaning of the statement

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U011.Statements`.
No other import is needed. Its unchanged import chain U011 Statements →
U010 Definitions → U009 Proofs → U009 Statements → U008 Proofs → U008
Statements → U007 → U006 Proofs → U006 Statements → U005 → U004 → U003 →
U002 → U001 → NormUnits/U002 supplies these existing constructions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L      -- QuotientGroup.mk' (localNormSubgroup K L)
normQuotientEquivOfSubgroupEq K L N h : NormQuotient K L ≃* (Kˣ ⧸ N)
                                           -- QuotientGroup.quotientMulEquivOfEq h
```

So `localNormSubgroup K L` is the actual image of the unit norm map
`Lˣ → Kˣ`. `NormQuotient K L` is `Kˣ` modulo that image, with the
published group instance `normQuotientCommGroup K L`. `normClass K L x` is
the class of `x` in `NormQuotient K L`. The equivalence
`normQuotientEquivOfSubgroupEq K L N h` is the published M093.010
definition, whose body is Mathlib's `QuotientGroup.quotientMulEquivOfEq h`.
The right-hand side `(QuotientGroup.mk x : Kˣ ⧸ N)` is the canonical class
of `x` in Mathlib's quotient group `Kˣ ⧸ N`. This module uses these
constructions as they are. It defines no new subgroup, quotient,
projection, equivalence or instance.

## Implemented proof

```lean
theorem normQuotientEquivOfSubgroupEq_normClass :
    NormQuotientEquivOfSubgroupEqNormClassStatement.{u} := by
  intro K L _ _ _ N h x
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x
```

The statement constant is an ordinary definition whose value is the
universally quantified proposition above. The tactic `intro` unfolds it
and introduces the eight binders: the fields `K` and `L`, the three
anonymous instances, the subgroup `N`, the equality `h` and the unit `x`.
The goal is now

```lean
normQuotientEquivOfSubgroupEq K L N h (normClass K L x) = (QuotientGroup.mk x : Kˣ ⧸ N)
```

The `change` step replaces this goal by a definitionally equal one on the
concrete quotients:

```lean
QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) = QuotientGroup.mk x
```

Here the left `QuotientGroup.mk x` lies in `Kˣ ⧸ localNormSubgroup K L`
(the domain of the equivalence, fixed by the left side of `h`), and the
right one lies in `Kˣ ⧸ N`. Lean accepts the change because both goals
unfold to the same term: `NormQuotient K L` is by definition
`Kˣ ⧸ localNormSubgroup K L`; the published
`normQuotientEquivOfSubgroupEq K L N h` is by definition
`QuotientGroup.quotientMulEquivOfEq h`; and the published `normClass K L`
is by definition `QuotientGroup.mk' (localNormSubgroup K L)`, whose value
at `x` is `QuotientGroup.mk x`. The normality instances that
`quotientMulEquivOfEq` and both quotient groups need are found by instance
search, as Mathlib's `Subgroup.normal_of_isMulCommutative`.

The last step applies Mathlib's `QuotientGroup.quotientMulEquivOfEq_mk`
to `h` and `x`. In the approved Mathlib,
`Mathlib/GroupTheory/QuotientGroup/Basic.lean` lines 162–168 define
`QuotientGroup.quotientMulEquivOfEq`, and lines 170–173 state and prove
(by `rfl`) the lemma

```lean
theorem quotientMulEquivOfEq_mk {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) (x : G) :
    QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) = QuotientGroup.mk x
```

With `G = Kˣ`, `M = localNormSubgroup K L` and the given `N`, this is
exactly the changed goal. The proof uses no `simp` call, rewriting, new
lemma or new instance.

This is the closed-target adaptation of the source proof. In the source,
the eight binders are parameters of the theorem and the proof is the
`change` and `exact` lines (lines 111–113). Here the eight binders lie
inside the proposition, so the proof first introduces them; the `change`
and `exact` lines are the source proof unchanged.

A second route also works: after introducing the eight binders, `rfl`
closes the goal, since Mathlib's lemma is itself proved by `rfl`. A
private development check confirmed this. The implemented proof keeps the
source route because it names the reused Mathlib lemma, as the task
requests.

## General norm convention

The dependencies keep Mathlib's unrestricted `Algebra.norm K`, which needs
no finite-module hypothesis. In the approved
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define the norm as the
determinant of multiplication. Lines 76–79 prove
`Algebra.norm_eq_one_of_not_module_finite`: the norm is constantly `1`
when `L` is not a finite `K`-module. Then `localNormSubgroup K L` is the
trivial subgroup, `h` can hold only for `N = ⊥`, and the theorem says that
the equivalence sends the class of `x` to the class of `x` in `Kˣ ⧸ ⊥`.
The proof above does not depend on finiteness, so it covers this case
without change. Results that need finiteness add it themselves.

## Scope

This module adds exactly the named theorem, without a simp registration
or a convenience theorem. It proves only the representative equation for
the published equivalence `normQuotientEquivOfSubgroupEq`. It does not
prove the inverse map's equation, the equivalence between two norm
quotients (source unit M093.012) or any later unit. It gives no exact norm
kernel, finiteness or index result, quotient topology, continuity, Artin
map, reciprocity law, host quotient, host evaluation or host adapter. The
parent obligations for the actual Artin map, the exact norm kernel, the
host quotient and its evaluation, continuity and reciprocity remain open.
This theorem does not complete the parent finite reciprocity task.

## Source and adaptation

This is the proof phase of source unit M093.011 in the published NYLL
declaration partition `notes/reuse/nyll-public-port/m073-m096.md` (line
726), where it follows `M093.010.END`. The original is Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, kept in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The relative source path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`
(verified again for this task).

Lines 1–125 of the 381-line original were read again for this task.
Lines 1–5 carry the attribution. Line 24 declares the universes `u v`.
Lines 26–54 hold the subgroup, quotient, group instance, representation
equivalence and class map. Lines 93–101 hold the published equivalence
`normQuotientEquivOfSubgroupEq` (M093.010). The selected theorem is lines
103–113, quoted exactly:

```lean
/-- After identifying the norm subgroup with another subgroup, a norm class maps to the
corresponding quotient class. -/
@[simp]
theorem normQuotientEquivOfSubgroupEq_normClass
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N) (x : Kˣ) :
    normQuotientEquivOfSubgroupEq K L N h (normClass K L x) =
      QuotientGroup.mk x := by
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x
```

The docstring is lines 103–104, the `simp` attribute line 105, the
statement lines 106–110 and the proof lines 110–113. The definition
`normQuotientEquivOfNormSubgroupEq` (lines 115–122, M093.012) and all
later declarations are excluded.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientEquivOfSubgroupEq_normClass` | `Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSubgroupEq_normClass` |

Worker 1097 added the `Langlands.NYLL` namespace prefix and gave the
theorem the already published closed statement constant as its type. The
eight source parameters now lie inside that proposition, so the proof
introduces them first. The `change` and `exact` lines are unchanged. The
original docstring is kept verbatim. The equation and the shared field
universe are unchanged. The `@[simp]` attribute, the unused universe `v`,
the source-wide imports, the `noncomputable section` and all other source
declarations are omitted. A theorem needs no noncomputable section. The
target's Lean/Markdown pair and every imported dependency pair are
preserved byte for byte. The published partition records no patch10
change to this module.

In the pinned source tree, this theorem is used in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`
line 186, inside a `rw` call that names it explicitly. That use belongs
to a later module and is not ported here; it does not rely on the omitted
simp registration.

Fresh searches of TaskHub tasks (for
`normQuotientEquivOfSubgroupEq_normClass`), the current Library, staged
candidates, shared drafts and the approved Mathlib found no existing
proof of this target. They found only the published statement, its
statement task, the M093.010 definition record that excludes this unit,
this task, and verbatim copies of the source file in shared draft
`b66bd2bc-abd3-4ea5-ae34-af7cdbeac0a3`, which were not reused. Mathlib's
`QuotientGroup.quotientMulEquivOfEq_mk` is the generic equation on
concrete quotients; it does not mention the named `NormQuotient`,
`normClass` or `normQuotientEquivOfSubgroupEq`, so it is reused rather
than duplicated.

Errata locations in the workspace, the project, the literature folder and
the current Library were checked for both the source registration above
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable erratum was found.

## Development checks

The approved Lean service (environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled this module with
zero errors and zero warnings. Inspection reports a theorem with the
single universe parameter `u`. Its recorded type is exactly the constant
`Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfSubgroupEqNormClassStatement.{u}`,
with no other binders. The only recorded axioms are `propext`,
`Classical.choice` and `Quot.sound`.

A separate private probe confirmed that the declared type is
structurally equal to that constant, that the `rfl` route described above
also proves the target, and that the theorem applies with fields in
`Type` and in `Type 2`. These checks are development evidence only. They
are not independent semantic review.

## Attribution

The original 2026 Naganori Yamaguchi copyright and author header is kept
verbatim, including “Naganori Yamaguchi (assisted by OpenAI Codex)”. The
source is licensed under Apache-2.0. The Lean file adds an explicit
modification record dated 30 October 2026. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are kept through the
submission's `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Both files are byte-identical to the original. The source NOTICE has no
third-party entry for NormQuotient, and the source's ValuedFieldTheory
list of included Anthropic FLT files does not include NormQuotient.lean.
Worker 1097 performed this adaptation. No other project worker
contributed code or a reused draft to this unit.
