# Uniform continuity and unique continuous extension of orbit maps

Authors: Worker 6 and Worker 1126.

This module contains statement targets only: three Prop-valued definitions
and one closed master target. It proves none of them. The proof is a
separate exact-target successor task.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained source is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The original conventions and I.1.1–I.1.3, printed pp.5–9/PDF11–15, were
read for this module.

- The conventions and I.1.1–I.1.2 supply nonunital associative rings, their
  modules, idempotents and their order, finite local units, and
  nondegenerate modules (every vector is fixed by some idempotent).
- I.1.3, printed p.8/PDF14, gives `A` the topology with zero-neighborhood
  basis `A(1-e)`. It defines `Ā` as the inverse limit of the right images
  `Ae`. Printed p.9/PDF15 describes `Ā` as compatible families, gives it the
  topology with zero-neighborhood basis `Ā(1-e) = {ā | ā(e) = 0}`, and
  embeds `A` by `a ↦ ā`, `ā(e) = a e`. The same page proves that `A` is
  dense in `Ā`.
- The last paragraph of I.1.3, printed p.9/PDF15, defines the action on a
  nondegenerate module `M`: if `e · m = m`, then `ā · m = ā(e) · m`. It says
  that this does not depend on `e` and makes `M` a unital `Ā`-module. It
  ends: "Autrement dit, si M est muni de la topologie discrète,
  l'application uniformément continue A → M, a ↦ a · m se prolonge par
  continuité à Ā."

The registered 2010-edition errata `renard-2010-corrections-complements`
concern the pseudometric order and a local-unit formula. The 2026 text
already prints both corrections, and neither concerns this paragraph.

## Objects used

All targets use published constructions, imported by Lean name from
`Langlands.Algebra.IdempotentedRingRightLimitAction` and
`Langlands.Algebra.IdempotentedRingRightLimitUniformity`. Throughout,
`A : Type uA` and `M : Type uM` have independent universes and carry their
original `NonUnitalRing A`, `AddCommGroup M` and `NonUnitalModule A M`.
The scalar action `a • m` is the given one.

- `idempotentedRingUniformSpace A` is the published uniformity on `A`. It is
  the infimum over all idempotents `e` of the pullbacks of the discrete
  uniformity along `a ↦ a * e`. This realizes the source topology with zero
  neighborhoods `A(1-e)`.
- `IdempotentedRingRightLimit A` is the published carrier of compatible
  families, the source's `Ā`. `IdempotentedRingRightLimit.canonical` is the
  published canonical additive map `a ↦ (e ↦ a * e)`, the source's `a ↦ ā`.
- `IdempotentedRingRightLimit.uniformSpace A` is the published family
  uniformity. It is the infimum over all idempotents `e` of the pullbacks of
  the discrete uniformity along `x ↦ x(e)`.
- `IdempotentedRingRightLimitAction.act hM x m`, for
  `hM : IsNondegenerate A M`, is the published action. It is
  `x(e₀) • m`, where `e₀` is the idempotent fixing `m` chosen from `hM m`.
  The published `act_eq` shows, under `IsIdempotented A`, that every fixing
  idempotent `e` gives `act hM x m = x(e) • m`. This is the source's
  independence of the choice.
- The codomain `M` carries the discrete uniformity `(⊥ : UniformSpace M)`.
  Its topology is the discrete topology `⊥`.

None of these uniformities is a global instance. Every statement passes the
domain and codomain uniformity or topology explicitly with `@`, so no
inferred subtype or substitute topology can occur. No statement has a
topology parameter, a replacement action, or an assumed continuity,
extension or uniqueness certificate.

## The three statements

- `IdempotentedRingOriginalOrbitUniform A M` is
  `∀ m : M, @UniformContinuous A M (idempotentedRingUniformSpace A) ⊥ (fun a => a • m)`.
  Every original orbit map is uniformly continuous from the actual
  uniformity of `A` into discrete `M`.
- `IdempotentedRingRightLimitOrbitUniform A M hM` is
  `∀ m : M, @UniformContinuous (IdempotentedRingRightLimit A) M (IdempotentedRingRightLimit.uniformSpace A) ⊥ (fun x => act hM x m)`.
  Every actual extended orbit map is uniformly continuous from the actual
  family uniformity into discrete `M`.
- `IdempotentedRingRightLimitOrbitContinuousExtension A M hM` says, for every
  `m : M`, three things. The domain topology is that of
  `IdempotentedRingRightLimit.uniformSpace A`, and the codomain topology is
  that of `(⊥ : UniformSpace M)`.
  1. `fun x => act hM x m` is continuous.
  2. `act hM (canonical a) m = a • m` for every `a : A`.
  3. Every continuous `f : IdempotentedRingRightLimit A → M` with
     `f (canonical a) = a • m` for every `a` equals `fun x => act hM x m`.

  The competitor `f` in clause 3 is an arbitrary continuous function. It is
  not required to be additive, equivariant or uniformly continuous.

These definitions carry no `IsIdempotented A` hypothesis. The second and third
take `hM` only because `act` needs it. The master target below says under
which hypotheses they are asserted.

## Master target

`IdempotentedRingOrbitExtensionTheorem` (universes `uA`, `uM`) is

```
∀ (A : Type uA) (M : Type uM)
  [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
  IsIdempotented A → ∀ hM : IsNondegenerate A M,
    IdempotentedRingOriginalOrbitUniform A M ∧
    IdempotentedRingRightLimitOrbitUniform A M hM ∧
    IdempotentedRingRightLimitOrbitContinuousExtension A M hM
```

All three statements are asserted under the published finite-local-unit
condition `IsIdempotented A` and nondegeneracy `hM`. There is no global unit,
original unit-action law, commutativity, nontriviality, field, countability,
dimension or finiteness hypothesis. Zero rings, trivial carriers and
noncommutative nonunital rings are included.

Nondegeneracy matters already for the first statement, which does not
mention `hM`. Let `A` be the finitely supported functions `ℕ → ℤ` with
pointwise operations. It has finite local units, given by indicators of
finite sets. Let `M` be all functions `ℕ → ℤ` with pointwise action. The
orbit map of the constant function `1` is the inclusion `a ↦ a`. Every
entourage of `A` contains `{(a, b) | a * e = b * e}` for the indicator `e` of
some finite set. It therefore contains a pair `(0, b)` with `b ≠ 0`
supported outside that set. So this orbit map is not uniformly continuous
into discrete `M`. Here `1` is fixed by no idempotent. This example is for
explanation only and is not proved in Lean here.

## Checks in the Lean file

- Complete unapplied `example` checks give each of the three definitions its
  full type at arbitrary universes `uA`, `uM`. The master is checked to have
  type `Prop`.
- `rfl` checks unfold the master to the displayed formula at arbitrary
  universes and at both unequal assignments `(0,1)` and `(1,0)`.
- `rfl` checks show the following.
  - The topology of `(⊥ : UniformSpace M)` is Mathlib's discrete topology `⊥`.
  - `a • m` is the original action, `NonUnitalModule.toEndHom inst a m`.
  - The two uniform-continuity statements agree with the plain Mathlib
    statements when the actual uniformities are installed locally with `let`.
- One example derives the continuity clause from the second statement with
  `UniformContinuous.continuous`. This confirms that both use the same
  topology.
- One example turns the third statement into
  `∃! f, Continuous f ∧ ∀ a, f (canonical a) = a • m`, with the same explicit
  topologies.
- Two examples specialize the master target. One gives canonical
  compatibility for any `IsIdempotented` ring and nondegenerate module. The
  other applies it at universes `(0,0)` to the zero ring `PUnit.{1}` acting by
  zero on the trivial carrier `PUnit.{1}`, where both hypotheses are proved.

`lean_check` inspection reports the master declaration as returning `Prop`,
with level parameters `uA`, `uM`. Its only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

- **Uniform continuity of the original orbit** is stated in the source's
  last sentence of I.1.3 ("l'application uniformément continue"), with no
  printed proof.
- **Continuity and canonical restriction of the extended orbit** are the
  source's "se prolonge par continuité à Ā". Its "Autrement dit" identifies
  this extension with the action `ā(e) · m`. Clauses 1 and 2 state this for
  the published `act`. The canonical restriction is also the published
  `canonical_act`, which uses `IsIdempotented A`.
- **Uniform continuity of the extended orbit** is an internal strengthening
  of the source's continuity.
- **Uniqueness among all continuous extensions** is an internal consequence.
  The source does not state it.

The intended route is guidance only and is not a premise of any target. If
`e • m = m`, then `a • m = (a * e) • m`, so the original orbit is constant on
the entourage `{(a, b) | a * e = b * e}`. Likewise the extended orbit is
constant on `{(x, y) | x(e) = y(e)}`. Continuity follows from uniform
continuity, and canonical restriction from `canonical_act`. For uniqueness,
the codomain is discrete and Hausdorff, and the canonical image is dense in
`Ā`. That density is the source's argument on PDF15. It is a component of
the published statement `IdempotentedRingRightLimitDensityCompletenessTheorem`.
A proof of the orbit statements that uses density must use the
independently published proof of that statement.

## Remaining obligations

Proving the master target is a separate exact-target proof task, to be
published after this statement is accepted and published. The following
are also outside this module:

- the uniform equivalence of `Ā` with `UniformSpace.Completion`;
- continuity of the limit multiplication;
- categorical equivalences of module categories;
- the completion of a nondegenerate module in I.1.4.
