# Renard B.III: separation for the original nonunital action

This module states three propositions and their universally quantified
conjunction. They cover the separation lemma for the original possibly
nonunital complex algebra, including its one-sided shift and its actual
unitization quotient. They assert no separation proof. The examples check
complete declaration types, canonical quotient instances, the restriction
of the action, and its value on the class of `1`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Appendix B.III is printed p. 273 / PDF p. 279. The lemma asserts that a
nonnilpotent element of a countable-dimensional complex algebra acts
nontrivially on some simple left module. Its proof adjoins a scalar unit,
obtains a nonzero scalar shift without a left inverse, takes a simple
quotient of the resulting principal-left-ideal quotient, and uses the class
of the unit to show that the original element acts nontrivially. These
passages were read directly, together with B.I–II on PDF pp. 277–278.

The additive-module conventions are printed pp. 5–6 / PDF pp. 11–12.
I.2.1, printed p. 14 / PDF p. 20, distinguishes additive original-action
maps from complex-linear maps. A.VI.3, printed p. 263 / PDF p. 269, supplies
the source's general simple-quotient result. These passages were also read
directly. Here simplicity refers to all stable additive subgroups for the
specified original action, in agreement with those conventions.

No project errata file for the governing source was present at the source
audit. The registered old-edition corrections,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp. 18–19, were read. The B.III correction removes a false
right-zero-divisor assertion and keeps the one-sided absence of a left
inverse. The 2026 text already incorporates that correction. It governs
the present targets.

The source gives an existential simple module and constructs a quotient.
The explicit maximal-left-ideal witness, the specified original additive
action, and the three-target conjunction are derived implementation
packaging of that construction. The expanded additive restriction is an
obligation, not an assumption that restriction always preserves simplicity.
The unital propositions in `Langlands.Algebra.SeparationStatements` remain
separate, reusable intermediate targets.

## Actual algebra, quotient and action

Let `A : Type uA` have `[NonUnitalRing A] [Module ℂ A]`,
`[IsScalarTower ℂ A A]` and `[SMulCommClass ℂ A A]`. These are an
associative possibly noncommutative complex algebra with bilinear
multiplication. No unit of `A` is supplied. Write `U = Unitization ℂ A`,
Mathlib's actual scalar unitization, and `ι a = Unitization.inr a`.

A witness `I : Submodule U U` is a left ideal of the regular left module.
`IsCoatom I` says it is maximal among proper left ideals. The carrier
`Q = U ⧸ I` is the actual left-module quotient, and `I.mkQ : U →ₗ[U] Q`
is its canonical quotient map. No two-sidedness or quotient ring is
required. The complex module and the scalar tower on `Q` are inherited
from the canonical quotient instances.

In each quotient conclusion the homomorphism is explicitly

```lean
ρ : A →ₙₐ[ℂ] Module.End ℂ Q :=
  Unitization.lift.symm (_root_.Algebra.lsmul ℂ ℂ Q)
```

Here `Algebra.lsmul` is the actual canonical `U`-action homomorphism.
`Unitization.lift.symm` restricts it along the actual inclusion `ι`.
The original ambient action is exactly
`NonUnitalModule.ofLinearEndHom ρ`, installed locally with `letI`.
Its formula is

```text
a • m = (ι a) • m,
a • I.mkQ 1 = I.mkQ (ι a).
```

The module's examples check these formulas, the first by reflexivity.
The second follows by moving the scalar action through `I.mkQ` and
using `(ι a) * 1 = ι a`. Thus `a • I.mkQ 1 ≠ 0` supplies the original
lemma's separating vector. It also forces `ρ ≠ 0`; no separate
nonzero-action assumption is imposed.

Original additive simplicity is written out as

```text
Nontrivial Q ∧
  ∀ S : NonUnitalSubmodule A Q,
    S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤.
```

This quantifies over every original stable additive subgroup, without
requiring scalar stability. The `Nontrivial` conjunct excludes the zero
module. The original action and the canonical complex vector space
structure coexist; the latter does not restrict the subgroups quantified
here. The separate `IsSimpleModule U Q` conclusion records simplicity
for the actual unital quotient action as well.

## Declarations

Every declaration is in `Langlands.Renard`, is a `def` returning `Prop`,
and retains the arbitrary carrier universe `uA`. Each of the first three
has all five algebra binders explicitly in its declaration header.

| Declaration | Content |
| --- | --- |
| `NonUnitalNonnilpotentLeftResolventStatement A` | If `Module.rank ℂ A ≤ Cardinal.aleph0` and `a` is not nonunitally nilpotent, there is `z : ℂ`, `z ≠ 0`, such that no `b : U` satisfies `b * (ι a - algebraMap ℂ U z) = 1`. |
| `NonUnitalLeftShiftSimpleQuotientStatement A` | Given exactly such a nonzero shift without a left inverse, there is a maximal left ideal `I` containing `Submodule.span U {ι a - algebraMap ℂ U z}`. The actual quotient `Q` is simple under `U`, is explicitly additively simple under the restricted original `A`-action, and `a • I.mkQ 1 ≠ 0`. |
| `NonUnitalSeparationStatement A` | Under the countable rank bound, every original nonnilpotent `a` has an actual maximal-left-ideal quotient `Q` which is simple under `U`, explicitly additively simple under the restricted original action, and separated by its class of `1`. |
| `NonUnitalSeparationReductionStatement` | Universal quantification of the conjunction of the preceding three targets over every `A : Type uA` and its full algebra structure. |

`IsNonUnitalNilpotent a` is the published condition
`∃ n : ℕ, successorPower a n = 0`, where `successorPower a n` multiplies
`n + 1` copies of `a`. It requires no identity or zeroth power in `A`.
The published theorem `Langlands.Algebra.isNilpotent_inr_iff` compares
this condition with `IsNilpotent (ι a : U)`.

Countable dimension is the cardinal bound `Module.rank ℂ A ≤
Cardinal.aleph0`, allowing finite dimension and arbitrary countably infinite
dimension. It is not countability of the set `A`. The quotient step has no
dimension or nilpotence premise; those conditions are needed only for
obtaining the shift.

## Mathematical route and retained proof obligations

This is an explanation of the targets, not an implemented proof.

The published comparison `unitization_countableRank_iff` transfers the
rank bound to `U`. The positive-power comparison transfers nonnilpotence
to `ι a`. The unital one-sided resolvent target
`NonnilpotentLeftResolventStatement U` then supplies the shift.
Two-sided noninvertibility alone does not supply this conclusion.

The unital target `LeftShiftSimpleQuotientStatement U` supplies a maximal
left ideal containing the shift, a simple actual quotient, and the
separating class of `1`. To obtain original additive simplicity one must
justify restriction for this particular nonzero original action. The
separately published simplicity targets include
`CompatibleUnitization.SimpleUnitizationRestrictionStatement`; their
proof owner retains that obligation.

Concretely, the nonzero separating action excludes a nonzero original
annihilator in the simple unitized module. For any nonzero original stable
additive subgroup `S`, sums of elements `ρ a s` form a nonzero
complex-linear `U`-submodule contained in `S`: scalar closure follows
from `c • (ρ a s) = ρ (c • a) s`. Simplicity forces that submodule, and
hence `S`, to be the whole quotient. This explains why the original
additive conclusion is reasonable and why a simple unitized module with
zero original action would be insufficient. These arguments remain
proof obligations; the declarations assume none of their conclusions.
The final target combines the shift and quotient targets.

## Universes, zero cases and authorship

The field ℂ is in `Type`; `A` has arbitrary universe `uA`.
`U = Unitization ℂ A` and its actual quotient `Q` are in `Type uA`.
This witness universe comes from the actual source construction, rather
than from an externally chosen module carrier. No finite-dimensional,
commutative, topological, normed, or representation-theoretic hypothesis
is added.

There is no `Nontrivial A` premise. In a zero algebra each original element
has a vanishing positive product, so the nonnilpotent implications are
vacuous. Even in that case the unitization has its scalar summand, so it
must not be confused with the original zero algebra. In the quotient step
the nonzero shift of the original zero element is a nonzero scalar unit,
making the no-left-inverse premise impossible. The condition `z ≠ 0`
is essential: at `z = 0` the required ideal would contain `ι a`, which
would make the displayed separating action vanish.

Worker 709 formulated this original-action statement unit and checked its
actual quotient action. Worker 6 contributed the source-convention and
additive-restriction clarification, including the nonzero-action route.
Existing unital statement and proof authors and the separate simplicity
proof owner retain their work; this unit asserts none of their pending
proofs.

## Author checks

In Lean environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` the module
compiles without errors or warnings. The three component declarations and
the aggregate were inspected as proposition-valued definitions. Complete
unapplied signature and expanded-body probes preserve all five algebra
binders and the arbitrary algebra universe. The quotient-action examples
check the canonical scalar instances and the actual class-of-`1` formula.
These checks establish declaration typing and action formulas; the three
substantive targets remain unproved.
