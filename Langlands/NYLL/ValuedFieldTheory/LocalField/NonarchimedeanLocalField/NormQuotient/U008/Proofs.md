# Evaluation of a norm-quotient lift on norm classes

`Langlands.NYLL.LocalFieldTheory.normQuotientLift_normClass.{u, v}`
proves exactly the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientLiftNormClassStatement.{u, v}`.
The theorem's declared type is that statement constant itself, at the
universe parameters `u` and `v`. The theorem has no external term
parameters. The proposition contains all ten binders:

```lean
∀ {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L] [Group M]
  (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker) (x : Kˣ),
  Langlands.NYLL.LocalFieldTheory.normQuotientLift f h
      (Langlands.NYLL.LocalFieldTheory.normClass K L x) =
    f x
```

In words: if a homomorphism `f : Kˣ →* M` kills every norm, then the
homomorphism descended from `f` through the norm quotient sends the norm
class of every unit `x` to `f x`.

## Universes and binders

Both universes are arbitrary and independent. The fields `K` and `L`
share the universe `u`. The target group `M` lives in the universe `v`.
The statement keeps the source binder kinds: `K`, `L` and `M` are
implicit; `Field K`, `Field L`, `Algebra K L` and `Group M` are
instance-implicit; `f`, `h` and `x` are explicit. The target `M` is an
arbitrary group.

The only hypothesis is `h : localNormSubgroup K L ≤ f.ker`. The theorem
adds no finite-dimensionality, separability, Galois, local-field,
valuation, topology, surjectivity or exact-kernel premise, and no premise
that assumes the evaluation.

## Meaning of the hypothesis

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U008.Statements`.
Its unchanged import chain U008 Statements → U007 → U006 Proofs →
U006 Statements → U005 → U004 → U003 → U002 → U001 → NormUnits/U002
supplies these existing constructions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
```

So `localNormSubgroup K L` is the actual image of the unit norm map
`Lˣ → Kˣ`. The hypothesis `h` says that this image lies in the kernel of
`f`, that is, `f (Units.map (Algebra.norm K) y) = 1` for every unit `y`
of `L`. The kernel only has to contain the norms. It need not equal the
norm subgroup, and `f` need not be surjective.

The named quotient `NormQuotient K L` carries the published instance
`normQuotientCommGroup K L`. The published `normClass K L` is the
canonical class map `Kˣ →* NormQuotient K L`, and the published
`normQuotientLift f h` is the descended homomorphism
`NormQuotient K L →* M`. This module uses these constructions as they
are. It defines no new subgroup, quotient, projection, lift or instance.

## Implemented proof

```lean
theorem normQuotientLift_normClass :
    NormQuotientLiftNormClassStatement.{u, v} := by
  intro K L M _ _ _ _ f h x
  exact QuotientGroup.lift_mk (localNormSubgroup K L) h x
```

The statement constant is an ordinary definition whose value is the
universally quantified proposition above. The tactic `intro` unfolds it
and introduces the ten binders: the types `K`, `L`, `M`, the four
anonymous instances, the homomorphism `f`, the hypothesis `h` and the
unit `x`. This is the closed-target adaptation: in the source these ten
binders are parameters of the theorem, and here they are introduced from
the proposition.

The proof then applies Mathlib's `QuotientGroup.lift_mk`. In the approved
Mathlib, `Mathlib/GroupTheory/QuotientGroup/Defs.lean` lines 245–250
define `QuotientGroup.lift N φ HN : G ⧸ N →* M`, and lines 252–254 state

```lean
theorem lift_mk {φ : G →* M} (HN : N ≤ φ.ker) (g : G) :
    lift N φ HN (g : Q) = φ g
```

with proof `rfl`. Here `N` is `localNormSubgroup K L`, `HN` is `h`, `g`
is `x`, and `φ` is the implicit `f`, read off from the type of `h`. This
gives `QuotientGroup.lift (localNormSubgroup K L) f h (x : Kˣ ⧸
localNormSubgroup K L) = f x`. Its right side is the goal's right side.

`exact` accepts this term for the goal because the two left sides are
definitionally equal. Lean's definitional check at the default
transparency unfolds three ordinary published definitions:

- `NormQuotient K L` unfolds to `Kˣ ⧸ localNormSubgroup K L`;
- `normQuotientLift f h` unfolds to
  `QuotientGroup.lift (localNormSubgroup K L) f h`, because its body
  exposes the concrete quotient with `change`, names the subgroup `N`
  with a `let`, and returns `QuotientGroup.lift N f h`;
- `normClass K L` unfolds to `QuotientGroup.mk' (localNormSubgroup K L)`
  by the same pattern. In the approved Mathlib (same file, lines 86–89)
  `QuotientGroup.mk'` is built from `QuotientGroup.mk`, so
  `normClass K L x` reduces to the quotient class of `x`.

The published `normQuotientCommGroup K L` is the quotient-group
structure found by instance search on the concrete quotient, so the
homomorphism structures on both sides also agree after unfolding.
These definitions are ordinary semireducible definitions, not reducible
abbreviations. Their bodies are visible only at default transparency.
A private development check confirmed that `with_reducible rfl` does not
close the goal, while plain `rfl` does.

The original source proof is `rfl`. The adaptation uses the named Mathlib
theorem `QuotientGroup.lift_mk` instead. It rests on the same
definitional equation and records the generic quotient fact that the
proof reuses. No rewriting, `simp` call, new lemma or new instance is
used.

## General norm convention

The dependencies keep Mathlib's unrestricted `Algebra.norm K`, which needs
no finite-module hypothesis. In the approved
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define the norm as the
determinant of multiplication. Lines 76–79 prove
`Algebra.norm_eq_one_of_not_module_finite`: the norm is constantly `1`
when `L` is not a finite `K`-module. Then the norm image on units is the
trivial subgroup, every homomorphism `Kˣ →* M` satisfies `h`, and the
theorem gives the evaluation equation for the quotient by the trivial
subgroup. The proof above does not depend on finiteness, so it covers
this case without change. Results that need finiteness add it
themselves.

## Scope

This module adds exactly the named theorem, without a simp registration.
It proves only that the general descended homomorphism agrees with `f` on
norm classes. It does not prove surjectivity of the lift (source unit
M093.009), uniqueness of the lift, any quotient equivalence, an exact
norm kernel, finiteness of the quotient, continuity, an Artin map, a
reciprocity law or a norm-index result. It supplies no host adapter and
no convenience theorem. It does not complete the parent finite
reciprocity task.

## Source and adaptation

This is the proof phase of source unit M093.008 in the published NYLL
declaration partition `notes/reuse/nyll-public-port/m073-m096.md`. The
original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, kept in the registered
source `external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The relative source path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`
(verified again for this task).

Lines 1–95 of the 381-line original were read independently for this
task. Lines 1–5 carry the attribution. Line 24 declares the universes
`u v`. Lines 26–54 hold the subgroup, quotient, group instance,
representation equivalence and class map. Lines 65–72 hold
`normQuotientLift`. Lines 74–81 hold the selected theorem: its docstring
(lines 74–75), the `@[simp]` attribute (line 76), the statement (lines
77–80) and the proof `rfl` (line 81). The surjectivity theorem (lines
83–91) and all later declarations are excluded.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientLift_normClass` | `Langlands.NYLL.LocalFieldTheory.normQuotientLift_normClass` |

Worker 1078 added the `Langlands.NYLL` namespace prefix and gave the
theorem the already published closed statement constant as its type. The
ten source parameters now lie inside that proposition, so the proof
introduces them first. The proof applies `QuotientGroup.lift_mk` in place
of the original `rfl`. The original docstring is kept. The equation, the
two independent universes and the shared field universe are unchanged.
The `@[simp]` attribute, the source-wide imports, the `noncomputable
section` and all other source declarations are omitted. A theorem needs
no noncomputable section. The target's Lean/Markdown pair and every
imported dependency pair are preserved byte for byte.

Fresh searches of TaskHub tasks (for `normQuotientLift_normClass` and
`NormQuotientLiftNormClassStatement`), the current Library, staged
candidates, shared drafts and the approved Mathlib found no existing
proof of this target. They found only the published statement, its
predecessor tasks, this task, and verbatim copies of the source file in
the shared drafts. Mathlib's `QuotientGroup.lift_mk` is the generic
equation on a concrete quotient; it does not mention the named
`NormQuotient`, `normClass` or `normQuotientLift`, so it is reused rather
than duplicated. The host `Langlands.LocalClassField.finiteNormQuotientMap`
has a different finite-extension and topological scope and is not a
replacement for this target; no host declaration is changed here. The
published partition records no patch10 change to this module.

Errata locations in the workspace, the project and the current Library
were checked for both the source registration above and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable erratum was found.

## Development checks

The approved Lean service (environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled this module with
zero errors and zero warnings. Inspection reports a theorem with universe
parameters `u` and `v`. Its recorded type is exactly the constant
`Langlands.NYLL.LocalFieldTheory.NormQuotientLiftNormClassStatement.{u, v}`,
with no other binders. The only recorded axioms are `propext`,
`Classical.choice` and `Quot.sound`.

A separate private probe confirmed that the declared type is structurally
equal to that constant, that the original `rfl` proof also works after
`intro`, that `with_reducible rfl` fails, and that the theorem applies
with fields in `Type` and a target group in `Type 2`. These checks are
development evidence only. They are not independent semantic review.

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
Worker 1078 performed this adaptation. No other project worker
contributed code or a reused draft to this unit.
