# Proof of the actual forgetful natural-endomorphism classification

Authors: Worker 1170 (Lean proof and Markdown); Worker 1192 (recheck against
the published Library and source, submission).

This module proves the eight targets of
`Langlands.Algebra.NondegenerateModuleNaturalEndClassificationStatement`
(Worker 6 and Worker 1170) and their aggregate. It changes nothing in the
statement module or its imports. The final theorem is

```
Langlands.Algebra.NondegenerateModuleNaturalEndClassificationProof.classification :
  Classification.{uA, uM}
```

for arbitrary universes `uA` and `uM`. Its only hypotheses are those inside the
statement: an original `NonUnitalRing A` and `IsIdempotented A`. It has no
extra hypothesis. `lean_check` against the published statement (Library
commit `9a8ca758097242bde4147f33304f43fceef22fa4`) reports 0 errors, 0
warnings and the axioms `propext`, `Classical.choice` and `Quot.sound`.

The source is Renard, *Représentations des groupes réductifs p-adiques*
(2026), I.1.6, Proposition and its proof, printed pp.11–12/PDF17–18. The
statement Markdown records the provenance of each target. The source proof
says only that one checks easily that the action of `ā` is natural and that
"les deux constructions sont inverses l'une de l'autre". The proofs below
supply those two inverse checks. They use only the published action and
evaluation maps.

## Notation

- `R = IdempotentedRingRightLimit A`, with the named ring
  `IdempotentedRingRightLimit.ring hA`.
- `T = NondegenerateModuleNaturalEnd.{uA, max uA uM} A`, the natural
  endomorphisms of the forgetful functor from
  `NondegenerateModuleCat.{uA, max uA uM} A` to abelian groups, with the named
  ring `NondegenerateModuleNaturalEnd.ring`.
- `L = NondegenerateModuleNaturalEndEvaluation.liftedRegularObject hA`, the
  regular module `ULift A` with `a • up b = up (a * b)`.
- `F = IdempotentedRingRightLimit.toNaturalEndRingHom hA : R →+* T`. The
  component of `F x` at `M` is the published action of `x` on `M`.
- `G = NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom hA : T →+* R`.
  By definition `(G θ).val e = (θ.app L (up e)).down`.

## Imports

- `Langlands.Algebra.NondegenerateModuleNaturalEndClassificationStatement`,
  the target statements.

The published lemmas used are
`IdempotentedRingRightLimit.toNaturalEndRingHom_app_eq` (if `e • m = m` then
`(F x).app M m = x.val e • m`), the definition of `G` above, and the
defining property `x.val e * e = x.val e` of a compatible right family. The
rest is from Mathlib.

## Auxiliary declarations

- `orbitMap hA M m : L ⟶ M` is the original intertwiner `up a ↦ a • m`. It is
  additive by `zero_smul` and `add_smul`, and it is `A`-linear by `mul_smul`.
  `orbitMap_apply` records its value (`rfl`).
- `app_eq_evaluation_smul`: if `e • m = m`, then
  `θ.app M m = (θ.app L (up e)).down • m`. Proof: naturality of `θ` along
  `orbitMap hA M m`, evaluated at `up e`, says
  `θ.app M (e • m) = (θ.app L (up e)).down • m`. Rewriting `e • m` to `m`
  gives the claim. The source applies naturality only to right
  multiplications of `A`, to see that `θ_A` lies in `Ā`. Naturality along the
  orbit maps is the step it leaves to the reader in "les deux constructions
  sont inverses l'une de l'autre".

## Proofs of the targets

1. `coordinateRecovery` (target 7, `(G (F x)).val e = x.val e`). By
   definition the left side is `((F x).app L (up e)).down`. Since `e` is
   idempotent, `e • up e = up e` holds in `L`. So
   `toNaturalEndRingHom_app_eq` gives `(F x).app L (up e) = x.val e • up e`.
   Its `down` is `x.val e * e`, which equals `x.val e` by the family property.
2. `familyRecovery` (target 3, `G (F x) = x`). Subtype extensionality and
   function extensionality over `e`, then target 7.
3. `componentPointRecovery` (target 6, `(F (G θ)).app M m = θ.app M m`).
   Since `M` is nondegenerate, choose `e` with `e • m = m`. Then
   `toNaturalEndRingHom_app_eq` rewrites the left side to
   `(G θ).val e • m`, and `app_eq_evaluation_smul` rewrites the right side to
   `(θ.app L (up e)).down • m`. The two are equal by the definition of `G`.
4. `componentRecovery` (target 5, equality of the whole additive components).
   `AddMonoidHom.ext` and target 6.
5. `naturalEndRecovery` (target 4, `F (G θ) = θ`). `NatTrans.ext`, function
   extensionality over `M`, `AddCommGrpCat.hom_ext`, then target 5.
6. `familyCompositeIdentity` (target 1, `G.comp F = RingHom.id R`) and
   `naturalEndCompositeIdentity` (target 2, `F.comp G = RingHom.id T`).
   `RingHom.ext` applied to targets 3 and 4. These two proofs and the next
   one bind the named rings with `let _`, as the statements do with `letI`.
7. `specifiedRingEquivalence` (target 8). The witness is
   `RingEquiv.ofRingHom F G h₁ h₂`, with `h₁` target 2 and `h₂` target 1.
   Its forward function is `F` and its inverse function is `G` by `rfl`.
8. `classification`. Introduce `A`, the original ring and `hA`, and return
   the eight results in the statement's order.

## Relation to the source

The route follows Renard's proof. The forward map is the action of `ā` on
each nondegenerate module (the published `F`), and the backward map is
evaluation at the regular module (the published `G`). The source works with
`A` itself. The statement uses the lifted regular object `L` at carrier
universe `max uA uM`, so that `L` is an object of the same category as the
modules `M`. The proofs above do not change universes.
