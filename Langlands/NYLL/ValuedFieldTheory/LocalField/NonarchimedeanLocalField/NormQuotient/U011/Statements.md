# The subgroup-equality norm-quotient equivalence on representatives

`Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfSubgroupEqNormClassStatement.{u}`
is the following closed proposition:

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
  (N : Subgroup Kˣ) (h : Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L = N) (x : Kˣ),
  Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSubgroupEq K L N h
      (Langlands.NYLL.LocalFieldTheory.normClass K L x) =
    (QuotientGroup.mk x : Kˣ ⧸ N)
```

It says: let `N` be a subgroup of `Kˣ` and let `h` say that `N` equals the
norm subgroup. Then the published equivalence
`normQuotientEquivOfSubgroupEq K L N h : NormQuotient K L ≃* Kˣ ⧸ N` sends
the norm class of any unit `x : Kˣ` to the class of the same unit `x`
modulo `N`. In words, the equivalence keeps representatives.

This artifact is an unproved statement interface. It only defines the
target proposition. It does not prove it.

## Declaration shape

The declaration itself has type `Prop` and no parameters. It is an ordinary
definition (not a theorem and not an assumption), and its value is the
universally quantified proposition above. It has one universe parameter,
`u`. It is arbitrary, and the two fields `K` and `L` share it.

All eight binders of the source theorem are quantified inside the
proposition, in source order and with their source binder kinds:

- the fields `K` and `L` are explicit;
- `Field K`, `Field L` and `Algebra K L` are instance-implicit;
- the subgroup `N`, the equality `h` and the unit `x` are explicit.

There is one hypothesis, `h : localNormSubgroup K L = N`. There is no
premise that `N` is normal. `Kˣ` is commutative, so every subgroup of it is
normal, and Lean infers this. There is no finite-dimensionality,
separability, Galois, local-field, valuation, topology, surjectivity or
exact-kernel premise.

The right-hand side carries the type annotation `Kˣ ⧸ N`. The source writes
only `QuotientGroup.mk x` and lets Lean infer the type from the left-hand
side. Both forms elaborate to the same proposition (see the development
checks below).

## Meaning of the proposition

The only direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U010.Definitions`,
as the task requires. It is the module of source unit M093.010. Its
unchanged published chain U010 Definitions → U009 Proofs → U009 Statements →
U008 Proofs → U008 Statements → U007 → U006 Proofs → U006 Statements → U005
→ U004 → U003 → U002 → U001 → NormUnits/U002 supplies these constructions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L      -- QuotientGroup.mk' (localNormSubgroup K L)
normQuotientEquivOfSubgroupEq K L N h : NormQuotient K L ≃* (Kˣ ⧸ N)
                                           -- QuotientGroup.quotientMulEquivOfEq h
```

So `localNormSubgroup K L` is the actual image of the unit norm map
`Lˣ → Kˣ`. `NormQuotient K L` is `Kˣ` modulo that image, with the published
group instance `normQuotientCommGroup K L`. `normClass K L x` is the class
of `x` in `NormQuotient K L`. The equivalence
`normQuotientEquivOfSubgroupEq K L N h` is the published M093.010
definition. Its body is Mathlib's `QuotientGroup.quotientMulEquivOfEq h`.

The left-hand side applies that equivalence, as a function, to the norm
class of `x`. The right-hand side `(QuotientGroup.mk x : Kˣ ⧸ N)` is the
canonical class of `x` in Mathlib's quotient group `Kˣ ⧸ N`, which is the
coset of `x` modulo `N`. Both sides live in `Kˣ ⧸ N`. The statement
introduces no new subgroup, quotient, projection, equivalence or instance.

The target `Kˣ ⧸ N` carries Mathlib's group structure
`QuotientGroup.Quotient.group N`. It needs `N` to be normal. Lean finds this
by instance search, as Mathlib's `Subgroup.normal_of_isMulCommutative`
(`Mathlib/Algebra/Group/Subgroup/Defs.lean` lines 629–631). During
elaboration Lean stores that proof as the auto-generated auxiliary theorem
`NormQuotientEquivOfSubgroupEqNormClassStatement._proof_1 :
∀ (K : Type u_1) [Field K] (N : Subgroup Kˣ), N.Normal`, whose value is
`fun K _ N => Subgroup.normal_of_isMulCommutative N`. It is an
implementation detail, not a premise and not a public interface.

In the approved Mathlib, `Mathlib/GroupTheory/QuotientGroup/Basic.lean`
lines 170–173 state `QuotientGroup.quotientMulEquivOfEq_mk`: the equivalence
`QuotientGroup.quotientMulEquivOfEq h` sends the class of `x` to the class
of `x`, by `rfl`. That lemma is the generic version of this statement on
concrete quotients. It does not mention the named `NormQuotient`,
`normClass` or `normQuotientEquivOfSubgroupEq`. The source proof (lines
110–113) uses `change` to expose the concrete quotient and then applies that
lemma. A later exact proof may follow the same route.

## General norm convention

The dependencies keep Mathlib's unrestricted `Algebra.norm K`, which is
defined without a finite-module hypothesis. In
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define the norm as the
determinant of multiplication. Lines 76–79 state and prove
`Algebra.norm_eq_one_of_not_module_finite`: the norm is constantly `1` when
`L` is not a finite `K`-module. In that case `localNormSubgroup K L` is the
trivial subgroup `⊥`, the hypothesis `h` can hold only for `N = ⊥`, and the
proposition says that the equivalence sends the class of `x` to the class
of `x` in `Kˣ ⧸ ⊥`. This case is part of the statement, which is why no
finiteness premise is added. Results that need finiteness add it
themselves.

## Scope

This proposition is only the representative equation for the published
equivalence `normQuotientEquivOfSubgroupEq`. It does not state or prove the
inverse map's equation, multiplicativity, uniqueness of the equivalence,
the equivalence between two norm quotients (source unit M093.012) or any
later unit. It gives no exact norm kernel, finiteness or index result,
quotient topology, continuity, Artin map, reciprocity law, host quotient,
host evaluation or host adapter. It contains no theorem, no `simp`
registration and no proof of this target under another name. Publication
of this target leaves its separate exact proof obligation open, and it does
not complete the parent finite reciprocity task.

## Source and adaptation

This is the statement phase of source unit M093.011 in the published NYLL
declaration partition `notes/reuse/nyll-public-port/m073-m096.md` (line
726), where it follows `M093.010.END`. The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, kept in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The relative source path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`
(verified again for this task).

Lines 1–125 of the 381-line original were read for this task. Lines 1–5
carry the attribution. Line 24 declares the universes `u v`. Lines 26–101
hold the published subgroup, quotient, group instance, representation
equivalence, class map, lift, their theorems and the published
equivalence `normQuotientEquivOfSubgroupEq` (lines 93–101, M093.010). The
selected passage is lines 103–113, quoted exactly:

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
`normQuotientEquivOfNormSubgroupEq` (lines 115–122, M093.012) and all later
declarations are excluded.

| Original declaration | Adapted statement |
| --- | --- |
| `LocalFieldTheory.normQuotientEquivOfSubgroupEq_normClass` | `Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfSubgroupEqNormClassStatement` |

Worker 1097 converted the source theorem into a closed proposition. Every
binder of the theorem telescope moved, with its name and binder kind, into
universal quantification inside `Prop`. The conclusion and the shared field
universe are unchanged. Worker 1097 added the namespace prefix, the type
annotation `Kˣ ⧸ N` on the right-hand side, a modification record and this
documentation. The docstring adds a universe remark to the original wording.
The source proof (lines 110–113) and the `@[simp]` attribute (line 105) are
omitted; a proposition definition is not a rewrite rule. The source universe
`v` is not used and is omitted, so `u` is the only universe. The
source-wide imports, `noncomputable section` and all other source
declarations are omitted; the single published U010 Definitions import
supplies everything needed, and a proposition needs no noncomputable
section. The original theorem name
`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSubgroupEq_normClass`
is reserved for a separate later exact proof. The published partition
records no patch10 change to this module.

In the pinned source tree, this theorem is used in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`
line 186, as a rewriting step. That use belongs to a later module and is
not ported here.

The related registration `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The errata locations in the workspace, the project, the literature folder
and the current Library were checked for both registrations. No applicable
erratum was found.

Fresh searches of TaskHub tasks (for
`NormQuotientEquivOfSubgroupEqNormClassStatement` and
`normQuotientEquivOfSubgroupEq_normClass`), the current Library, staged
candidates, shared drafts and the approved Mathlib found no existing target
and no duplicate task. They found only this task, the predecessor's
exclusion, the partition entry, and verbatim copies of the source file in
shared draft `b66bd2bc-abd3-4ea5-ae34-af7cdbeac0a3`, which were not reused.
Mathlib's `QuotientGroup.quotientMulEquivOfEq_mk` is the generic fact on
concrete quotients, not this named closed statement.

## Development checks

The approved Lean service (environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled U010 Definitions and
this Statements module with zero errors and zero warnings. Inspection of the
exact unapplied declaration reports an ordinary definition, the single
universe parameter `u`, and `statement_returns_prop: true`. The complete
unapplied type is `Prop`. The only recorded assumptions are `propext`,
`Classical.choice` and `Quot.sound`.

A separate private probe built with zero errors and zero warnings. It checks
that:

- the declaration is a regular, safe definition of type `Prop` with
  universe parameters `[u]`;
- its value has exactly the eight binders listed above, with those names,
  binder kinds and universes;
- the conclusion is an equation in `Kˣ ⧸ N`, whose left side is the function
  application of `normQuotientEquivOfSubgroupEq K L N h` to
  `normClass K L x` and whose right side is `QuotientGroup.mk` applied to
  `Kˣ`, its unit group structure, `N` and `x`;
- the proposition is `Iff.rfl`-equivalent to the source theorem's telescope
  and conclusion written without the type annotation;
- its value is structurally identical to that source form except for the
  name of the auxiliary normality theorem, whose type and value are the same
  in both;
- the proposition can be instantiated with fields in `Type` and in
  `Type 2`;
- when `L` is not a finite `K`-module, the norm subgroup is trivial.

The probe also confirmed feasibility. The target follows by the source
route, which changes the goal to the concrete quotient and applies
`QuotientGroup.quotientMulEquivOfEq_mk`. It also follows by `rfl` after
introducing the binders. These private checks are not part of the public
candidate. They are development evidence, not a public proof of the target
and not independent semantic acceptance.

## Attribution

The original 2026 Naganori Yamaguchi copyright and author header is kept
verbatim, including “Naganori Yamaguchi (assisted by OpenAI Codex)”. The
source is licensed under Apache-2.0. The Lean file adds an explicit
modification record dated 30 October 2026. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are kept through the
submission's `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Both
files are byte-identical to the original. The source NOTICE has no
third-party entry for NormQuotient, and the source's ValuedFieldTheory
list of included Anthropic FLT files does not include NormQuotient.lean.
Worker 1097 performed this adaptation. No other project worker contributed
code or a reused draft to this unit.
