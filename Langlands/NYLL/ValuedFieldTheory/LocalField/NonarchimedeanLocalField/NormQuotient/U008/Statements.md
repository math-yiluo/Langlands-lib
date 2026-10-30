# Evaluation of a norm-quotient lift on norm classes

`Langlands.NYLL.LocalFieldTheory.NormQuotientLiftNormClassStatement.{u, v}`
is the following closed proposition:

```lean
∀ {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L] [Group M]
  (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker) (x : Kˣ),
  Langlands.NYLL.LocalFieldTheory.normQuotientLift f h
      (Langlands.NYLL.LocalFieldTheory.normClass K L x) =
    f x
```

It says: if a homomorphism `f : Kˣ →* M` kills every norm, then the
homomorphism descended from `f` through the norm quotient sends the norm
class of every unit `x` to `f x`. In words, the descended homomorphism agrees
with `f` on representatives.

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
- the homomorphism `f`, the hypothesis `h` and the unit `x` are explicit.

The only hypothesis is `h : localNormSubgroup K L ≤ f.ker`. There is no
finite-dimensionality, separability, Galois, local-field, valuation,
topology, surjectivity or exact-kernel premise, and no premise that assumes
the evaluation. The target `M` is an arbitrary group, as in the source.

This artifact only defines the target proposition. It does not prove the
equation.

## Meaning of the equation

The only direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U007.Definitions`.
Its chain U007 → U006 Proofs → U006 Statements → U005 → U004 → U003 → U002
→ U001 → NormUnits/U002 supplies these existing constructions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
```

So `localNormSubgroup K L` is the actual image of the unit norm map
`Lˣ → Kˣ`. The hypothesis `h` says that this image lies in the kernel of
`f`. Equivalently, `f (Units.map (Algebra.norm K) y) = 1` for every unit
`y` of `L`. It only asks that the kernel contain the norms. It does not ask
that the kernel equal the norm subgroup, and it does not ask that `f` be
surjective.

The equation uses exactly two published constructions:

- `normClass K L : Kˣ →* NormQuotient K L` is the canonical class map. Its
  body exposes the concrete quotient, names the subgroup `N` and returns
  Mathlib's `QuotientGroup.mk' N`.
- `normQuotientLift f h : NormQuotient K L →* M` is the published descended
  homomorphism. Its body exposes the concrete quotient, names the same
  subgroup `N` and returns Mathlib's `QuotientGroup.lift N f h`.

The named quotient carries the published instance `normQuotientCommGroup K L`.
Both sides of the equation are elements of the supplied group `M`: the left
side applies `normQuotientLift f h` to `normClass K L x`, and the right side
applies `f` to `x`. The statement introduces no new subgroup, quotient,
projection, lift or instance.

`NormQuotient`, `normClass` and `normQuotientLift` are ordinary
semireducible definitions, not reducible abbreviations. Their bodies are
exposed only at Lean's default transparency. In the approved Mathlib,
`Mathlib/GroupTheory/QuotientGroup/Defs.lean` lines 245–250 define
`QuotientGroup.lift`, and lines 252–254 state `QuotientGroup.lift_mk`: on
the class of `g`, the lift returns `φ g`, with proof `rfl`. This is the
generic form of the target equation on the concrete quotient. A later exact
proof can reuse it after exposing the named definitions.

## General norm convention

The dependencies keep Mathlib's unrestricted `Algebra.norm K`, which is
defined without a finite-module hypothesis. In
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define the norm as the
determinant of multiplication. Lines 76–79 state and prove
`Algebra.norm_eq_one_of_not_module_finite`: the norm is constantly `1` when
`L` is not a finite `K`-module. In that case the norm image on units is the
trivial subgroup, every homomorphism `Kˣ →* M` satisfies `h`, and the
proposition still asserts the evaluation equation for the quotient by the
trivial subgroup. This is why no finiteness premise is added. Results that
need finiteness add it themselves.

## Scope

This proposition is only the evaluation equation of the descended
homomorphism. It does not state or prove surjectivity of the lift (source
unit M093.009), uniqueness of the lift, any quotient equivalence, an exact
norm kernel, finiteness of the quotient, continuity, an Artin map, a
reciprocity law or any norm-index result. It gives no host quotient
equivalence or host adapter. Publication of this target leaves its separate
exact proof obligation open, and it does not complete the parent finite
reciprocity task.

## Source and adaptation

This is the statement phase of source unit M093.008 in the published NYLL
declaration partition `notes/reuse/nyll-public-port/m073-m096.md`, where it
follows `M093.007.END`. The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, kept in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The relative source path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

Lines 1–110 of the 381-line original were read in full for this task, and
the declaration headers of the rest of the file were listed. Lines 1–5 carry
the attribution. Line 24 declares the universes `u v`. Lines 26–54 hold the
published subgroup, quotient, group instance, representation equivalence
and class map. Lines 65–72 hold the published `normQuotientLift`. Lines
74–81 hold the selected theorem: its docstring (lines 74–75), the `@[simp]`
attribute (line 76), the statement (lines 77–80) and the proof `rfl`
(line 81). The surjectivity theorem (lines 83–91) and all later
declarations are excluded.

| Original declaration | Adapted statement |
| --- | --- |
| `LocalFieldTheory.normQuotientLift_normClass` | `Langlands.NYLL.LocalFieldTheory.NormQuotientLiftNormClassStatement` |

Worker 248 converted the source theorem into a closed proposition. Every
term binder of the theorem telescope moved, with its binder kind, into
universal quantification inside `Prop`. The equation, both universes and
the shared field universe are unchanged. Worker 248 added the namespace
prefix, a modification record and this documentation. The source proof
`rfl` and the `@[simp]` registration are omitted. The source-wide imports,
`noncomputable section` and all other source declarations are omitted; the
single published U007 import supplies everything needed, and a proposition
needs no noncomputable section. The original theorem name
`Langlands.NYLL.LocalFieldTheory.normQuotientLift_normClass` is reserved for
a separate later exact proof. The published partition records no patch10
change to this module.

In the source, this theorem is used by the surjectivity theorem (line 91),
by `normQuotientMapOfLE_normClass` (line 229) and in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ArchimedeanNormQuotient.lean`
line 181. Those uses belong to later units and are not ported here.

The related registration `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The errata locations in the workspace, the project and the current Library
were checked for both registrations. No applicable erratum was found.

Fresh searches of TaskHub tasks, the current Library, staged candidates,
shared drafts and the approved Mathlib found no existing
`normQuotientLift_normClass` target and no duplicate task. The shared
drafts contain only a verbatim copy of the source file. Mathlib's
`QuotientGroup.lift_mk` is the generic equation on a concrete quotient; it
does not mention the named `NormQuotient`, `normClass` or
`normQuotientLift`. The host `Langlands.LocalClassField.finiteNormQuotientMap`
in `Langlands/ClassFieldTheory/Local/FiniteArtin.lean` has no evaluation
theorem of this form, and no host declaration is changed or compared here.

## Development checks

The approved Lean service (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled the dependency-first
module list ending in this Statements module with zero errors and zero
warnings. Inspection of the exact declaration reports an ordinary
definition, universe parameters `u` and `v`, and
`statement_returns_prop: true`. The complete unapplied type is `Prop`. The
only recorded assumptions are `propext`, `Classical.choice` and
`Quot.sound`.

A separate private probe built without errors; its only warning is a
deprecation notice inside the probe's own metaprogram. It checks that:

- the declaration's value has exactly the ten binders listed above, with
  those binder kinds and universes;
- the equation is an equality in `M`, its left side uses the published
  `normQuotientLift` and `normClass` with the published group instance on
  the named quotient, and its right side is the application of `f`;
- the proposition is `Iff.rfl`-equivalent to the source theorem's
  telescope;
- the proposition can be instantiated with fields in `Type` and a target
  group in `Type 2`;
- when `L` is not a finite `K`-module, the norm subgroup is trivial.

The probe also confirmed feasibility: the target follows by `rfl` at
default transparency, and also by unfolding `normQuotientLift` and
`normClass` and applying `QuotientGroup.lift_mk`. It does not follow by
`with_reducible rfl`. These private checks are not part of the public
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
third-party entry specific to NormQuotient. Worker 248 performed this
adaptation. No other project worker contributed code or a reused draft to
this unit.
