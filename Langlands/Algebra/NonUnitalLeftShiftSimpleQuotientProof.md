# Renard B.III: the actual quotient with its original additive action

`Langlands.Renard.nonUnitalLeftShiftSimpleQuotient` proves the unchanged
`NonUnitalLeftShiftSimpleQuotientStatement A`. It keeps the arbitrary
universe `uA` and exactly the original five algebra binders. There is no
countability or nilpotence hypothesis in this conditional quotient step.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
B.III, printed p. 273 / PDF p. 279, constructs a simple quotient of the
principal-left-ideal quotient of the unitized algebra. The source conventions
on printed pp. 5–6 / PDF pp. 11–12 allow nonunital algebras and original
additive modules. I.2.1, printed p. 14 / PDF p. 20, explains scalar
unitization; A.VI.3, printed p. 263 / PDF p. 269, defines simplicity by
all subobjects. These passages were read directly. The target Markdown's
older-edition correction context is preserved; the 2026 text governs.

The specified restricted action and its comparison with the canonical
quotient action are derived implementation details of the source
construction. This proof consumes the published unital quotient and
actual-action simplicity results and supplies only the small adapter
needed to identify their module structures.

## Implemented quotient and restriction

Write `U = Unitization ℂ A`. Applied at `U` and `Unitization.inr a`, the
published `Langlands.Renard.leftShiftSimpleQuotient` supplies exactly a
left ideal `I : Submodule U U` which is a coatom and contains
`Submodule.span U {Unitization.inr a - algebraMap ℂ U z}`. On the actual
carrier `Q = U ⧸ I`, the canonical `U`-module is simple and
`(Unitization.inr a : U) • I.mkQ 1 ≠ 0`.

The original action homomorphism is precisely

```lean
ρ : A →ₙₐ[ℂ] Module.End ℂ Q :=
  Unitization.lift.symm (_root_.Algebra.lsmul ℂ ℂ Q)
```

Its value `ρ a m` is definitionally `(Unitization.inr a : U) • m` under
the canonical quotient action. In particular, if `ρ = 0`, its value on
the actual class `I.mkQ 1` vanishes, contradicting the separating action
already supplied by the unital proof. Thus `ρ ≠ 0` is derived here.

The named adapter `Langlands.Renard.unitizationQuotient_module_eq` proves
equality of the entire `Module U Q` structures:
`CompatibleUnitization.module ρ` equals the canonical quotient structure.
It applies the published `module_unique_of_isScalarTower` to that canonical
structure and its canonical complex scalar tower. The agreement on all
embedded elements is definitional. Uniqueness extends this agreement to
every `x : U` using its scalar and original coordinates. This compares
the actual actions on one carrier; no replacement quotient or action is
introduced.

The proof rewrites by that equality to transport canonical simplicity to
`CompatibleUnitization.module ρ`. It then applies the independently
published `CompatibleUnitization.simpleUnitizationRestriction ρ` with the
derived `ρ ≠ 0`. Its conclusion installs exactly
`NonUnitalModule.ofLinearEndHom ρ` and yields `Nontrivial Q` and

```text
∀ S : NonUnitalSubmodule A Q,
  S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤.
```

These are all original stable additive subgroups, with no requirement of
complex scalar stability. Finally, `a • I.mkQ 1` for that local original
action is definitionally the nonzero separating expression above. The
class formula `a • I.mkQ 1 = I.mkQ (Unitization.inr a)` follows from
linearity of `I.mkQ` and `(Unitization.inr a) * 1 = Unitization.inr a`,
as checked in the unchanged target module.

The result retains both unitized simplicity and original additive
simplicity, the coatom condition, principal-left-ideal containment and
separation of the actual class of `1`. No two-sided ideal, quotient ring,
nontriviality of `A`, nonzero-action, commutativity, dimension or nilpotence
premise is added. The nonzero scalar shift and absence of a left inverse
are exactly the conditional target's premises.

Worker 1210 implemented this adapter and assembly. Worker 709 supplied the
original target and proposed route; Worker 6 supplied the original-action
and nonzero-action clarification. The imported unital quotient proof is
Worker 1210's published work. The imported simplicity engine is Worker
751's published work with Worker 6's annihilator and orbit route; those
existing publications and authorship are unchanged.

## Verification

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, the development check
compiled the module with zero errors and warnings. Declaration inspection
retains the sole universe parameter `uA` and only `propext`,
`Classical.choice` and `Quot.sound`. The submission's independent review,
Lake build and exact-target validation remain separate publication gates.
