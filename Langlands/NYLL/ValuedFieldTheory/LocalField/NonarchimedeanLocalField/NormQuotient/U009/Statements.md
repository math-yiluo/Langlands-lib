# Surjectivity of a norm-quotient lift

`Langlands.NYLL.LocalFieldTheory.NormQuotientLiftSurjectiveStatement.{u, v}`
is the following closed proposition:

```lean
∀ {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L] [Group M]
  (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker) (hf : Function.Surjective f),
  Function.Surjective (Langlands.NYLL.LocalFieldTheory.normQuotientLift f h)
```

It says: let `f : Kˣ →* M` be a homomorphism that kills every norm. If `f`
is surjective, then the homomorphism descended from `f` through the norm
quotient is also surjective. Every element of `M` is the value of the
descended homomorphism at some norm class.

## Declaration shape

The declaration itself has type `Prop` and no term parameters. It is an
ordinary definition, and its value is the universally quantified proposition
above. It has two universe parameters, `u` and `v`, and both are arbitrary.
The fields `K` and `L` share the universe `u`. The target group `M` lives in
the independent universe `v`.

All ten binders of the source theorem are quantified inside the proposition,
with their source binder kinds:

- `K`, `L` and `M` are implicit;
- `Field K`, `Field L`, `Algebra K L` and `Group M` are instance-implicit;
- the homomorphism `f`, the hypothesis `h` and the hypothesis `hf` are
  explicit.

There are two hypotheses. The first is `h : localNormSubgroup K L ≤ f.ker`.
The second, and the only surjectivity premise, is
`hf : Function.Surjective f`, which is surjectivity of the original
homomorphism `f`. There is no finite-dimensionality, separability, Galois,
local-field, valuation, topology or exact-kernel premise. There is also no
premise that assumes surjectivity of the lift. The target `M` is an
arbitrary group, as in the source.

The proposition never mentions the name `hf`. The binder keeps its source
name anyway, so that the statement reads like the source theorem. Lean's
unused-variables linter would warn about this, so the Lean file turns that
linter off for this one declaration with
`set_option linter.unusedVariables false in`. The option only affects
linting. It does not change the proposition.

This artifact only defines the target proposition. It does not prove
surjectivity.

## Meaning of the proposition

The only direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U008.Proofs`,
as the task requires. It is the module that ends source unit M093.008. Its
unchanged chain U008 Proofs → U008 Statements → U007 → U006 Proofs → U006
Statements → U005 → U004 → U003 → U002 → U001 → NormUnits/U002 supplies
these existing constructions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
```

So `localNormSubgroup K L` is the actual image of the unit norm map
`Lˣ → Kˣ`. The hypothesis `h` says that this image lies in the kernel of
`f`. Equivalently, `f (Units.map (Algebra.norm K) y) = 1` for every unit
`y` of `L`. It only asks that the kernel contain the norms. It does not ask
that the kernel equal the norm subgroup.

The conclusion uses the published construction
`normQuotientLift f h : NormQuotient K L →* M`. Its body exposes the
concrete quotient, names the subgroup `N` and returns Mathlib's
`QuotientGroup.lift N f h`. The named quotient `NormQuotient K L` carries
the published instance `normQuotientCommGroup K L`. The conclusion
`Function.Surjective (normQuotientLift f h)` says that for every `y : M`
there is a norm class `q : NormQuotient K L` with
`normQuotientLift f h q = y`. The statement introduces no new subgroup,
quotient, projection, lift or instance.

`NormQuotient`, `normClass` and `normQuotientLift` are ordinary
semireducible definitions, not reducible abbreviations. The published
theorem `normQuotientLift_normClass`, from the imported U008 Proofs module,
says that `normQuotientLift f h (normClass K L x) = f x` for every unit
`x`. The source proof uses exactly this: it picks a preimage `x` of `y`
under `f` and takes the class `normClass K L x`. In the approved Mathlib,
`Mathlib/GroupTheory/QuotientGroup/Defs.lean` lines 271–274 state
`QuotientGroup.lift_surjective_of_surjective`: the lift of a surjective
homomorphism through a concrete quotient is surjective. That lemma is the
generic version of this statement on the concrete quotient `G ⧸ N`. It does
not mention the named `NormQuotient` or `normQuotientLift`. A later exact
proof may reuse either route.

## General norm convention

The dependencies keep Mathlib's unrestricted `Algebra.norm K`, which is
defined without a finite-module hypothesis. In
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define the norm as the
determinant of multiplication. Lines 76–79 state and prove
`Algebra.norm_eq_one_of_not_module_finite`: the norm is constantly `1` when
`L` is not a finite `K`-module. In that case the norm image on units is the
trivial subgroup, and every homomorphism `Kˣ →* M` satisfies `h`. The
proposition then says that a surjective `f` stays surjective after passing
to the quotient of `Kˣ` by the trivial subgroup. This case is part of the
statement, which is why no finiteness premise is added. Results that need
finiteness add it themselves.

## Scope

This proposition is only the surjectivity assertion for the descended
homomorphism. It does not state or prove the evaluation equation (source
unit M093.008, already published with its proof), uniqueness of the lift,
any quotient equivalence (source units M093.010 and later), an exact norm
kernel, finiteness of the quotient, continuity, an Artin map, a reciprocity
law or any norm-index result. It contains no theorem, no simp registration
and no proof of this target under another name. It gives no host quotient
equivalence or host adapter. Publication of this target leaves its separate
exact proof obligation open, and it does not complete the parent finite
reciprocity task.

## Source and adaptation

This is the statement phase of source unit M093.009 in the published NYLL
declaration partition `notes/reuse/nyll-public-port/m073-m096.md`, where it
follows `M093.008.END`. The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, kept in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The relative source path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`
(verified again for this task).

Lines 1–130 of the 381-line original were read for this task. Lines 1–5
carry the attribution. Line 24 declares the universes `u v`. Lines 26–54
hold the published subgroup, quotient, group instance, representation
equivalence and class map. Lines 65–72 hold the published
`normQuotientLift`, and lines 74–81 hold the published evaluation theorem.
The selected passage is lines 83–91, quoted exactly:

```lean
/-- A map obtained by descending a surjective homomorphism through the norm
quotient is still surjective. -/
theorem normQuotientLift_surjective {K L : Type u} {M : Type v} [Field K] [Field L]
    [Algebra K L] [Group M] (f : Kˣ →* M)
    (h : localNormSubgroup K L ≤ f.ker) (hf : Function.Surjective f) :
    Function.Surjective (normQuotientLift f h) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨normClass K L x, normQuotientLift_normClass f h x⟩
```

The docstring is lines 83–84, the statement lines 85–88 and the proof
lines 89–91. `normQuotientEquivOfSubgroupEq` (line 96, M093.010) and all
later declarations are excluded.

| Original declaration | Adapted statement |
| --- | --- |
| `LocalFieldTheory.normQuotientLift_surjective` | `Langlands.NYLL.LocalFieldTheory.NormQuotientLiftSurjectiveStatement` |

Worker 1078 converted the source theorem into a closed proposition. Every
term binder of the theorem telescope moved, with its name and binder kind,
into universal quantification inside `Prop`. The conclusion, both universes
and the shared field universe are unchanged. Worker 1078 added the
namespace prefix, the local linter option described above, a modification
record and this documentation. The docstring adds the universe remark to
the original wording. The source proof (lines 89–91) is omitted. The
source-wide imports, `noncomputable section` and all other source
declarations are omitted; the single published U008 Proofs import supplies
everything needed, and a proposition needs no noncomputable section. The
original theorem name
`Langlands.NYLL.LocalFieldTheory.normQuotientLift_surjective` is reserved
for a separate later exact proof. The published partition records no
patch10 change to this module.

In the source, this theorem is used in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`
line 85, to show that the map from the norm quotient to the unramified
valuation quotient is surjective. That use belongs to a later module and is
not ported here.

The related registration `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The errata locations in the workspace, the project, the literature folder
and the current Library were checked for both registrations. No applicable
erratum was found.

Fresh searches of TaskHub tasks (for `normQuotientLift_surjective`,
`NormQuotientLiftSurjectiveStatement` and `M093.009`), the current Library,
staged candidates, shared drafts and the approved Mathlib found no existing
target and no duplicate task. They found only predecessor exclusions, this
task, the partition entry, and verbatim copies of the source file in the
shared drafts. Mathlib's `QuotientGroup.lift_surjective_of_surjective` is
the generic fact on a concrete quotient, not this named closed statement.

## Development checks

The approved Lean service (environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled the dependency-first
module list from NormUnits/U002 through U008 Proofs, ending in this
Statements module, with zero errors and zero warnings. Inspection of the
exact declaration reports an ordinary definition, universe parameters `u`
and `v`, and `statement_returns_prop: true`. The complete unapplied type is
`Prop`. The only recorded assumptions are `propext`, `Classical.choice` and
`Quot.sound`.

A separate private probe built without errors; its only warning is a
deprecation notice inside the probe's own metaprogram. It checks that:

- the declaration's value has exactly the ten binders listed above, with
  those names, binder kinds and universes;
- the conclusion is `Function.Surjective` applied to the published
  `normQuotientLift f h`;
- the proposition is `Iff.rfl`-equivalent to the source theorem's
  telescope;
- the proposition can be instantiated with fields in `Type` and a target
  group in `Type 2`;
- when `L` is not a finite `K`-module, the norm subgroup is trivial.

The probe also confirmed feasibility. The target follows by the source
route, which takes a preimage under `f` and applies the published
`normQuotientLift_normClass`. It also follows by applying
`QuotientGroup.lift_surjective_of_surjective` after introducing the
binders. These private checks are not part of the public candidate. They
are development evidence, not a public proof of the target and not
independent semantic acceptance.

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
Worker 1078 performed this adaptation. No other project worker contributed
code or a reused draft to this unit.
