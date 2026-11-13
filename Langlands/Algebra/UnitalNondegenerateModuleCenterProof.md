# Proof of the unital Remark of Renard I.1.7

Author: Worker 142 (Lean proof and Markdown), under Task 5709
(`56b7aa00-3ccf-44fb-9c6d-7f84b98504bd`).

This module proves the published statement
`Langlands.Algebra.UnitalNondegenerateModuleCenterStatement` from
`Langlands.Algebra.NondegenerateModuleCenterStatements`. It changes nothing in the statement
module or in anything that module imports. The final theorem is

```
Langlands.Algebra.UnitalNondegenerateModuleCenterProof.unitalNondegenerateModuleCenter :
  UnitalNondegenerateModuleCenterStatement.{uA, uM}
```

for arbitrary universes `uA` and `uM`. It adds no hypothesis: the only assumption is the one
inside the statement, a unital `Ring A`. `lean_check` reports 0 errors, 0 warnings and the
axioms `propext`, `Classical.choice` and `Quot.sound`.

The Theorem of I.1.7 for general rings with idempotents is proved separately, in
[NondegenerateModuleCenterProof](NondegenerateModuleCenterProof.md). This module does not
depend on it.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), I.1.7, Remarque,
printed p.13 / PDF p.19: "Lorsque `A` est unitaire, le centre `ℨ(A)` s'identifie au centre
de l'anneau `A`, résultat bien connu." The source gives no proof. The proof below is the
standard one: `z ↦ (m ↦ z • m)` and `θ ↦ θ_A(1)`. It is the route sketched in the statement
Markdown and the task context.

## Notation

- All modules are in `NondegenerateModuleCat.{uA, max uA uM} A`, the universe of the
  statement, and `NondegenerateModuleCenter.{uA, max uA uM} A` is its centre (natural
  endomorphisms of the identity functor).
- `L = NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA`, the regular
  module `ULift A` with `a • up b = up (a * b)`, where `hA = IsIdempotented.of_ring A`.

## Imports

- `Langlands.Algebra.NondegenerateModuleCenterStatements`: the target statement and the
  category, its centre and `NondegenerateModuleCenter.forget` (the forgetful image of a
  central `θ`, a natural endomorphism of the forgetful functor).
- `Langlands.Algebra.NondegenerateModuleNaturalEndClassificationProof`, for one lemma of the
  published proof of Renard I.1.6: `app_eq_evaluation_smul`. For a natural endomorphism `θ` of
  the forgetful functor, a module `M`, `m ∈ M` and an idempotent `e` with `e • m = m`, it says
  `θ_M m = (θ_L (up e)).down • m`. It comes from naturality of `θ` along the orbit map
  `L → M`, `up a ↦ a • m`.

Other published or Mathlib facts used: `IsIdempotented.of_ring`,
`exists_idempotent_smul_eq_iff_one_smul_eq` (for a unital ring, a vector is fixed by some
idempotent iff `1 • m = m`), `Subring.mem_center_iff`, `mul_smul`, and the module-map
property `map_smul` of the components of `θ`.

## Auxiliary declarations

- `scalarHom z M`: for `z` in the centre of `A`, multiplication `m ↦ z • m` as an original
  module map `M → M`. Additivity is `smul_zero` and `smul_add`. `A`-linearity,
  `z • (a • m) = a • (z • m)`, follows from `mul_smul` and `z * a = a * z`.
- `scalarCenter z`: the element of the centre of the category with components
  `scalarHom z M`. Naturality along a module map `f` is `f (z • m) = z • f m`, which is
  `map_smul` of `f`.

## Proof

**Part 1** (`existsUnique_center`): every `θ` acts as a unique central element. Put
`z = (θ_L (up 1)).down ∈ A`.

- *`θ` acts as `z`* (`hz`). Let `M` be a module and `m ∈ M`. Since `M` is nondegenerate,
  `1 • m = m` by `exists_idempotent_smul_eq_iff_one_smul_eq`. Then `app_eq_evaluation_smul`,
  applied to `forget θ` with the idempotent `1`, gives `θ_M m = z • m`.
- *`z` is central* (`hcomm`). Let `a ∈ A`. The component `θ_L` is `A`-linear, so
  `θ_L (a • up 1) = a • θ_L (up 1)`. On the left, `a • up 1 = up a`, and by `hz` at `L`,
  `θ_L (up a) = z • up a = up (z * a)`. The right side is `up (a * z)`. Taking `down` gives
  `z * a = a * z`.
- *Uniqueness.* If `w` is central and `θ_M m = w • m` for all `M` and `m`, then at `L` and
  `up 1` this gives `z = w * 1 = w`.

**Part 2** (every central element arises): for central `z`, the witness is
`scalarCenter z`. Its component at `M` applied to `m` is `z • m` by definition (`rfl`).

The final theorem `unitalNondegenerateModuleCenter` introduces `A` and its ring instance. It
returns Part 1 and Part 2, in the order of the statement.

## Relation to the source

This is the classical argument behind Renard's "résultat bien connu". It does not pass
through the completion `Â`, as the statement Markdown explains. The regular module `A`
appears as the lifted object `L`, so that it lies in the category at universe `max uA uM`.
