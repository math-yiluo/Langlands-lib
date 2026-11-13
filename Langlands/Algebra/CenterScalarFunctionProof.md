# Proof of Renard I.1.8: the centre as an algebra of functions on the irreducibles

Author: Worker 109 (Lean proof and Markdown), under Task 5710.

Module `Langlands.Algebra.CenterScalarFunctionProof`. It proves the published
proposition `Langlands.Algebra.CenterScalarFunctionStatement`
([statement Markdown](CenterScalarFunctionStatement.md)). The final theorem is

```
Langlands.Algebra.CenterScalarFunctionProof.centerScalarFunction :
  CenterScalarFunctionStatement.{uA, uM}
```

for arbitrary universes `uA` and `uM`. It adds no hypothesis and changes nothing in the
statement module or its imports. `lean_check` reports 0 errors, 0 warnings and the axioms
`propext`, `Classical.choice` and `Quot.sound`.

The source is David Renard, *Représentations des groupes réductifs p-adiques* (2026),
I.1.8, printed pp.13–14 / PDF pp.19–20. The statement Markdown quotes the passage. The
proof below follows Renard's route for the first three assertions. For the last assertion
(elements of `ℨ(A)` are determined by their scalars) it does not use the I.1.7
identification of `ℨ(A)` with the commutant of `A` in `Â`. It uses naturality along orbit
maps out of the regular module instead (step 4).

## Notation

- `A`: a complex algebra with idempotents (`NonUnitalRing A`, `Module ℂ A`,
  `IsScalarTower ℂ A A`, `SMulCommClass ℂ A A`, `hA : IsIdempotented A`), with
  `hrank : Module.rank ℂ A ≤ ℵ₀`.
- `M(A) = NondegenerateModuleCat.{uA, max uA uM} A` and
  `ℨ(A) = NondegenerateModuleCenter.{uA, max uA uM} A`, Mathlib's `CatCenter`, the natural
  endomorphisms of the identity functor of `M(A)`.
- `z_M m = (z.app M).hom.toAddMonoidHom m`. This is the statement's `acts z M m`.
- `c ·_M m = NondegenerateScalars.scalarMul ℂ M.property c m`, Renard's canonical scalars
  of I.2.1: `c · m = (c e) · m` for any idempotent `e` fixing `m`.
- `L = NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA`, the
  regular module `ULift A` with `a • up b = up (a * b)`, an object of `M(A)`.
- `orbitMap hA M m : L ⟶ M`, the published intertwiner `up a ↦ a • m`
  (`NondegenerateModuleNaturalEndClassificationProof.orbitMap`).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Algebra.CenterScalarFunctionStatement` | the target statement |
| `Langlands.Algebra.NonUnitalSchurProof` | `Langlands.Renard.nonUnitalSchurScalarOfAlgebraRankCountable` (B.II) |
| `Langlands.Algebra.NondegenerateModuleNaturalEndClassificationProof` | `orbitMap` (and, through its imports, `liftedRegularObject`) |

Other published declarations used: `NondegenerateScalars.module`,
`NondegenerateScalars.toLinearEndHom`, `NondegenerateScalars.map_scalarMul` (I.2.1),
`IdempotentedRingRightLimitAction.act_eq`, `IdempotentedRingRightLimit.ext`, the
compatibility law `x.val e * e = x.val e` of a right family, and Mathlib's `CatCenter.ext`
and `NatTrans.naturality`.

## Auxiliary lemmas

- `sub_smul`: `(a - b) • m = a • m - b • m` for an original action. It follows from
  `NonUnitalModule.add_smul` applied to `(a - b) + b`.
- `app_smul_eq hA z M m a`: `z_M (a • m) = (z_L (up a)).down • m`. This is the naturality
  square of `z` at `orbitMap hA M m` evaluated at `up a`: the orbit map sends `up a` to
  `a • m`, and sends `z_L (up a)` to `(z_L (up a)).down • m`. The proof is `congrArg` of
  `z.naturality (orbitMap hA M m)`.
- `scalar_of_iso hA z M N f c hc n`: if `z_M m = c ·_M m` for all `m` and `f : M ≅ N`,
  then `z_N n = c ·_N n`. Write `n = f(f⁻¹ n)` (from `f.inv_hom_id`). Naturality of `z` at
  `f.hom` gives `z_N (f(f⁻¹ n)) = f(z_M (f⁻¹ n)) = f(c ·_M f⁻¹ n)`. The published
  `NondegenerateScalars.map_scalarMul` (an intertwiner preserves the canonical scalars)
  turns this into `c ·_N f(f⁻¹ n) = c ·_N n`.

## The main proof

`centerScalarFunction` introduces `A`, its instances, `hA`, `hrank` and the two
`let`-bound names `IsSimple` and `acts`. It proves the three conjuncts separately.

1. **Scalars (B.II).** Let `z ∈ ℨ(A)` and let `M` be simple. Install the canonical complex
   module `NondegenerateScalars.module ℂ hA M.property` on `M.obj` locally. Its scalar
   multiplication is `scalarMul ℂ M.property` by definition. Let
   `ρ = NondegenerateScalars.toLinearEndHom ℂ hA M.property : A →ₙₐ[ℂ] Module.End ℂ M.obj`,
   the original action as a complex algebra map. The action `NonUnitalModule.ofLinearEndHom ρ`
   used by the Schur statements is definitionally the given action of `M`. So the
   simplicity hypothesis of the target is the one of B.II. The second component of
   `nonUnitalSchurScalarOfAlgebraRankCountable ρ hM hrank` gives, for the additive
   intertwiner `(z.app M).hom`, a unique `c : ℂ` with `z_M m = c • m = c ·_M m` for all
   `m`. This is the first conjunct.
2. **Class invariance.** Given `z`, simple `M ≅ N` (an isomorphism `f`) and `c` describing
   `z` on `M`, `scalar_of_iso` gives the conclusion. Simplicity is not used here.
3. **(Sep) implies faithfulness on `Â`.** Assume (Sep). Let `x ∈ Â` act by zero on every
   simple module. By `IdempotentedRingRightLimit.ext` it suffices to show `x.val e = 0`
   for every idempotent `e`. Otherwise (Sep) gives a simple `M` and `m` with
   `x.val e • m ≠ 0`. The vector `e • m` is fixed by `e`, since `e * e = e`. By
   `IdempotentedRingRightLimitAction.act_eq`, the action of `x` on `e • m` is
   `x.val e • (e • m) = (x.val e * e) • m = x.val e • m`, using `x.val e * e = x.val e`.
   This is nonzero, contradicting the hypothesis on `x`.
4. **(Sep) implies faithfulness on `ℨ(A)`.** Assume (Sep), and let `z, z' ∈ ℨ(A)` agree on
   every simple module. First, `(z_L (up e)).down = (z'_L (up e)).down` for every
   idempotent `e`. If their difference `d` were nonzero, (Sep) would give a simple `M` and
   `m` with `d • m ≠ 0`. But `app_smul_eq` gives `z_M (e • m) = (z_L (up e)).down • m`, and
   likewise for `z'`. The hypothesis at the vector `e • m` of `M` makes these equal, so
   `d • m = 0` by `sub_smul`, a contradiction. Next, `z = z'` by `CatCenter.ext`,
   `ObjectProperty.hom_ext` and `NonUnitalModuleHom.ext`. For `m` in any nondegenerate
   `M`, choose `e` with `e • m = m` (`M.property`). Then
   `z_M m = z_M (e • m) = (z_L (up e)).down • m = (z'_L (up e)).down • m = z'_M m`
   by `app_smul_eq` twice.

## Comparison with the source

Renard deduces the injectivity on `ℨ(A)` from the injectivity on `Â` through the I.1.7
identification of `ℨ(A)` with the commutant of `A` in `Â`. The Lean proof does not need
that identification, so the proof does not depend on the I.1.7 statement
`NondegenerateModuleCenterTheoremStatement`. Step 4 uses the evaluation `e ↦ z_L(up e)`,
which is the element of `Â` attached to `z` in I.1.6–I.1.7, but only through the
naturality identity `app_smul_eq`. Step 1 uses the countable-dimension form of B.II, as
Renard does.
