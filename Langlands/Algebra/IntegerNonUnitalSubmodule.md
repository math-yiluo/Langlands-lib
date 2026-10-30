# Integer-compatible submodules of original additive actions

Worker 709 prepared this derived construction. Its source motivation is
David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The conventions at printed pages 5–6 / PDF pages 11–12 permit
nonunital actions, including actions of a unital ring without a unit
law. I.2.1, printed page 14 / PDF page 20, distinguishes general
additive module morphisms from complex-linear ones; PDF page 21
supplies adjoining context. Worker 709 read these original passages
in the parent program, and Worker 1088 read them again for this
task. The registered older-edition supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 18–19, was also read by both. It does not supersede the
2026 original or settle its finiteness conventions. No project
errata file exists for either source.

This file is an internal adapter. The integer-unitization order
correspondence is derived from automatic integer compatibility and
the published generic compatible-submodule correspondence. It is
not asserted to occur in this form in Renard. The general
`CompatibleSubmodule.toNonUnitalSubmodule` is only an injection at
arbitrary coefficients, since a stable additive subgroup need not
be a subspace over those coefficients. Integer scalars give an inverse
because every additive subgroup is closed under integer multiplication.

The data are `A : Type uA` with `NonUnitalRing A`, `M : Type uM` with
`AddCommGroup M`, and the original `NonUnitalModule A M` instance.
The universes `uA` and `uM` are independent. There is no commutativity,
unit law, nondegeneracy, nontriviality, complex structure or finiteness
hypothesis. Zero carriers and zero actions are permitted.

Write `rho = NonUnitalModule.toIntLinearEndHom (A := A) (V := M)`.
Integer scalars on the ring and carrier are their canonical additive
group scalars. The original `A` action remains unchanged, including
when `A = Int` acts by zero. In that case the canonical scalar action
on `M` still comes from its additive group.

All declarations are in `Langlands.Algebra.NonUnitalSubmodule`.

`toIntCompatible S` uses Mathlib's actual
`AddSubgroup.toIntSubmodule` on `S.toAddSubgroup` and reuses
`S.smul_mem'` to prove stability under `rho`. Conversely,
`ofIntCompatible S` takes the actual underlying additive subgroup
of `S.toSubmodule` and uses `S.action_mem` for the original ambient
action. Both constructor types retain the original action instance.
The value of `rho a m` reduces to that original `a • m`; no action
structure is transported, replaced or installed as a global instance.

The two membership lemmas are reflexive. The round trips
`ofIntCompatible_toIntCompatible` and
`toIntCompatible_ofIntCompatible` follow by membership extensionality.
`intCompatibleOrderIso` packages these actual constructors, their
round trips and the reflexive preservation of inclusion.
Its forward and inverse evaluation lemmas are reflexive.

`intUnitizedOrderIso` composes `intCompatibleOrderIso` with the
unchanged published `CompatibleUnitization.submoduleOrderIso rho`.
Its codomain is the actual `Submodule (Unitization Int A) M`, using
exactly the locally selected `CompatibleUnitization.module rho`.
There is no arbitrary module argument or replacement carrier.
Forward and inverse membership and carrier-set equalities are
reflexive because both stages preserve the actual subset.
`intUnitizedOrderIso_le_iff` is the order isomorphism's inclusion law.
The structure itself supplies both round trips.

Private development checks, by Worker 709 and repeated by Worker
1088, compile the complete pair and inspect the
unapplied constructor and order-isomorphism types, their bodies, the
original action instance and the actual unitized module argument.
Universe applications at `(0,1)` and `(1,0)` compile. An independent
zero-action probe uses the even subgroup of the integers: it remains
a proper stable subgroup, its image contains two, and under the
actual unitized action the unit acts as identity while
`Unitization.inr (1 : Int)` acts as zero. The explicit `inr` matters
when both coordinates are integers. These checks give no independent
semantic acceptance and are excluded from the contribution.

These are definitions and intrinsic construction laws. This module
introduces no global instances, categories, scalar extension,
quotient constructions, finite-generation or Noetherian statements.
It does not identify Renard's finite-type conventions with ordinary
module finiteness over integer or complex unitization, and it does
not finish the final C.II proposition or the whole-book program.
