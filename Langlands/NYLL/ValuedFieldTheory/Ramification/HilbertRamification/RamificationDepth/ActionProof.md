# NYLL M323.001: unique-extension action preserves additive valuation (proof)

This module proves the published Library statement
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.addVal_valuationSubringAutOfUniqueExtensionStatement`
(module `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth.ActionStatement`)
by the theorem

```lean
theorem addVal_valuationSubringAutOfUniqueExtension :
    addVal_valuationSubringAutOfUniqueExtensionStatement.{u, v, w, x}
```

in namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`.
The theorem's type is exactly the closed statement, with all four universe
parameters `u v w x`; no binder, instance or hypothesis is added or removed.

## Source

The theorem name is the source theorem name
`RamificationTheory.HilbertRamification.Higher.addVal_valuationSubringAutOfUniqueExtension`
prefixed with `Langlands.NYLL`. The source is Naganori Yamaguchi's
*ClassFieldTheory*, pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationDepth.lean`,
lines 33–44 (section parameters at lines 20–29). The file's SHA-256 is
`443b4046f6fbacd7ad8760bfd6116ec5a4f182727e01d7fd931ce6e11eef0d1c`. It is in the registered
snapshot `external-lean-reuse-snapshots-2026-10-21`
(`n-yamaguchi-0729--ClassFieldTheory/source/...`).

## Mathematical content

Let `K` and `L` be fields, with `L` a `K`-algebra. Equip `K` with a discrete
valuation field structure `base` and `L` with one called `target`, in four
independent universes. Assume that `target.valuation` extends `base.valuation`
and that this extension is unique (`huniq`). Then each `K`-algebra automorphism
`σ` of `L` restricts to a ring automorphism of the valuation ring
`target.valuationSubring`. This is the published M304.014
`valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq σ`.
The theorem states that this automorphism preserves the normalized additive
valuation `IsDiscreteValuationRing.addVal` of every element `a` of the
valuation ring.

## Implemented proof

The proof introduces the binders of the closed proposition and makes one term
application:

```lean
exact _root_.IsDiscreteValuationRing.addVal_smul
  (valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq sigma) a
```

`IsDiscreteValuationRing.addVal_smul` is a published Library theorem, imported
from `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`.
Its statement is: for a discrete valuation ring `R` and a group `G` with a
`MulSemiringAction G R`, `addVal R (σ • x) = addVal R x` holds for all `σ : G`
and `x : R`. The proof uses it with:

- `R := target.valuationSubring`, a discrete valuation ring by the published DVF
  instances that the target statement itself uses;
- `G := target.valuationSubring ≃+* target.valuationSubring`, the group of ring
  automorphisms, with Mathlib's evaluation action
  `MulSemiringAction (R ≃+* R) R`, `e • a := e a`.

Lean infers `G` from the type of the M304.014 ring equivalence. Under this
action, `e • a` unfolds by definition to the evaluation `e a`. So the conclusion
of `addVal_smul` is definitionally the goal, and the term closes it without any
rewriting. The imported theorem is itself a pure ideal
argument: `x ∈ 𝔪ⁿ ↔ n ≤ addVal x`, and a semiring automorphism preserves every
power of the maximal ideal.

## Changes from the source route

The source proof is the one-line term
`IsDiscreteValuationRing.addVal_ringEquiv (valuationSubringAutOfUniqueExtension … huniq sigma) a`.
It uses the NYLL lemma `addVal_ringEquiv` (M311.002, from
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AddVal.lean`). This
proof replaces that call with the Library theorem `IsDiscreteValuationRing.addVal_smul`
specialized to the ring-automorphism action. No M311.002 target or proof is
needed, so neither is a prerequisite. The other changes are the namespace prefix
`Langlands.NYLL`, the closed-proposition form of the theorem type, and focused
imports. The two imports are the target statement module and the
lower-ramification-depth module above. No ramification-number, monogeneity,
uniformizer or Herbrand-average module is imported.

## Checks

A development `lean_check` of this module, inspecting the declaration, reported
0 errors and 0 warnings. The axioms it reported are exactly `propext`,
`Classical.choice` and `Quot.sound`. The proof uses no `sorry`, `admit`, new
axiom or `native_decide`. This is development evidence only: acceptance needs
independent review and the exact-target check.

## Attribution

The proof is adapted from Worker 313's unreviewed shared draft for Task 5884
(`42841808-c3ca-4957-8b90-6f6123f550b4`, draft revision 2). Worker 313 is
credited as coauthor. Naganori Yamaguchi's original copyright and author header
is retained in the Lean file, with a modification notice. `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` apply. The imported Anthropic-FLT module keeps its
own attribution (`licenses/Anthropic-FLT/`), and this file copies none of its
proof text.
