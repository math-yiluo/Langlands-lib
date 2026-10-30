# Stability criteria for compatible nonunital algebra actions: proofs

Author: Worker 1044.

This module proves the closed statement family of
`Langlands/Algebra/CompatibleStabilityStatements.lean`, which is imported
unchanged together with everything it imports. The family is an internal
specialization of David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix C.II, Definition and
Lemma (i)–(iii), printed pages 276–278 / PDF pages 282–284 (registered source
`renard-2026-representations-groupes-reductifs-padiques`). It applies them to
maps intertwining actual compatible actions of complex algebras. The statement
Markdown records the source correspondence and the provenance of this
specialization. The proof below does not follow the source argument directly.
It applies the published complex-linear criteria of
`Langlands.LinearAlgebra.StableEndomorphismProofs`, which formalize that
argument, to the underlying linear maps. It then moves kernels, ranges and
complementarity between the compatible-submodule lattice and the lattice of
ordinary subspaces.

All declarations are in the namespace `Langlands.Algebra.CompatibleStability`.

## Exported theorems

| Theorem | Proves exactly |
| --- | --- |
| `stableKernelRange` | `StableKernelRangeStatement.{uB, uV}` |
| `stableIffIsCompl` | `StableIffIsComplStatement.{uB, uV}` |
| `stableOfRightExact` | `StableOfRightExactStatement.{uB, uA, uM, uC}` |
| `stableOfLeftExact` | `StableOfLeftExactStatement.{uB, uA, uM, uC}` |
| `compatibleStability` | `CompatibleStabilityStatements.{uB, uV, uA, uM, uC}`, the aggregate, as the conjunction of the four theorems above in order |

Each theorem has the published closed proposition as its type and adds no
hypotheses. The level parameters of `compatibleStability` are `uB uV uA uM uC`,
in that order. These are the algebra universe, the single-space universe, and
the three independent exact-row carrier universes. A development check of the
unapplied theorem reported exactly these level parameters. It also reported
dependence on only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Actual objects and scope

The algebra `B` is any complex vector space with `[NonUnitalRing B]`,
`[IsScalarTower ℂ B B]` and `[SMulCommClass ℂ B B]`. It may be
noncommutative, have no unit, or be zero. Actions are the published
nonunital algebra homomorphisms `ρ : B →ₙₐ[ℂ] Module.End ℂ V`, including the
zero action, on arbitrary complex vector spaces, including the zero space.
Maps are the published `LinearIntertwiner`s, with their `toLinearMap`,
bundled `comp`, compatible `ker` and `range`. The lattice is the published
complete lattice `CompatibleSubmodule ρ`. Stability is the published
`Langlands.LinearAlgebra.StableEndomorphism.Stable` of the underlying
complex-linear endomorphism. No new predicate, carrier, action, kernel,
range or exactness object is constructed.

The helper lemmas omit the instances `IsScalarTower ℂ B B` and
`SMulCommClass ℂ B B`, which the proof never uses. The closed theorems
receive them as binders of the target propositions and simply do not use
them. There is no finite-dimensionality, finite generation, Noetherianity,
nondegeneracy, unit-action law, chain condition, splitting or countability
assumption anywhere.

## One-space helpers

Here `f : LinearIntertwiner ρ ρ` is a self-intertwiner of an arbitrary
compatible action `ρ` on `V`.

- `toLinearMap_comp_self`: `(f.comp f).toLinearMap = f.toLinearMap ^ 2`.
  The published `LinearIntertwiner.toLinearMap_comp` gives
  `f.toLinearMap ∘ₗ f.toLinearMap`. Mathlib's `pow_two` and
  `Module.End.mul_eq_comp` identify this composite with the square.
- `isCompl_iff_isCompl_toSubmodule`: for compatible submodules `S` and `T`,
  `IsCompl S T ↔ IsCompl S.toSubmodule T.toSubmodule`. Both directions use
  `disjoint_iff` and `codisjoint_iff`, which reduce complementarity to
  `S ⊓ T = ⊥` and `S ⊔ T = ⊤`. The published equations
  `CompatibleSubmodule.inf_toSubmodule`, `sup_toSubmodule`,
  `bot_toSubmodule` and `top_toSubmodule` say that `toSubmodule` preserves
  these operations. Rewriting along them carries each equation from the
  compatible lattice to the subspace lattice. In the converse direction,
  the rewritten equation is an equality of underlying subspaces, which
  `CompatibleSubmodule.toSubmodule_injective` lifts back to the compatible
  lattice.
- `stable_iff_ker_eq_and_range_eq` proves the body of
  `StableKernelRangeStatement`. `CompatibleSubmodule.toSubmodule_inj` turns
  both compatible equalities into equalities of underlying subspaces.
  The published `LinearIntertwiner.ker_toSubmodule` and `range_toSubmodule`
  identify these subspaces with `LinearMap.ker` and `LinearMap.range` of the
  underlying maps, and `toLinearMap_comp_self` replaces the bundled square.
  The result is the definition of `Stable f.toLinearMap`, closed by `rfl`.
- `stable_iff_isCompl_ker_range` proves the body of
  `StableIffIsComplStatement`. It rewrites `IsCompl f.ker f.range` by
  `isCompl_iff_isCompl_toSubmodule`, `ker_toSubmodule` and
  `range_toSubmodule` into
  `IsCompl (LinearMap.ker f.toLinearMap) (LinearMap.range f.toLinearMap)`.
  The published Lemma (i), `stable_iff_isCompl f.toLinearMap`, then finishes.

## Exact rows

Here `A`, `M` and `C` are complex vector spaces in independent universes,
with compatible actions `ρA`, `ρM` and `ρC` of the same algebra `B`. The maps
are `phi : LinearIntertwiner ρA ρM`, `psi : LinearIntertwiner ρM ρC`, and
self-intertwiners `fA`, `fM` and `fC`.

- `range_eq_ker_toLinearMap`: the compatible equality
  `phi.range = psi.ker` gives
  `LinearMap.range phi.toLinearMap = LinearMap.ker psi.toLinearMap`, by
  rewriting with `range_toSubmodule` and `ker_toSubmodule` and applying the
  hypothesis.
- `stable_of_rightExact_intertwiners` proves the body of
  `StableOfRightExactStatement`. It applies the published Lemma (ii),
  `stable_of_rightExact`, to `phi.toLinearMap`, `psi.toLinearMap`,
  `fA.toLinearMap`, `fM.toLinearMap` and `fC.toLinearMap`. Middle exactness
  comes from `range_eq_ker_toLinearMap`. The surjectivity of `psi` is
  passed unchanged, because the coercion of `psi` to a function agrees
  definitionally with that of `psi.toLinearMap`. The commuting squares are
  `congrArg LinearIntertwiner.toLinearMap` applied to the bundled equalities
  `fM.comp phi = phi.comp fA` and `fC.comp psi = psi.comp fM`. They
  give the linear-map squares definitionally, because the underlying map of
  a bundled composite is the composite of the underlying maps. The
  hypotheses `Stable fA.toLinearMap` and `Stable fM.toLinearMap` are passed
  unchanged.
- `stable_of_leftExact_intertwiners` proves the body of
  `StableOfLeftExactStatement` in the same way from the published
  Lemma (iii), `stable_of_leftExact`. It passes the injectivity of `phi`
  unchanged and transports middle exactness and both squares exactly as
  above. The hypotheses `Stable fM.toLinearMap` and `Stable fC.toLinearMap`
  are passed unchanged.

Only the one-sided endpoint conditions of the targets are used:
surjectivity of `psi` for the right-exact row and injectivity of `phi` for
the left-exact row. No opposite-endpoint condition or splitting is assumed.

## Closed statements

`stableKernelRange`, `stableIffIsCompl`, `stableOfRightExact` and
`stableOfLeftExact` introduce all algebras, instances, carriers, actions and
maps bound by the corresponding closed propositions. They then apply the
helpers above. `compatibleStability` is the anonymous-constructor
conjunction of these four theorems.

## Provenance and remaining obligations

The four components and their source correspondence are those of the
published statement pair by Workers 709 and 345. The route through the
published complex-linear theorems and the compatible-submodule lattice
operations follows the proof specification of task
`a80d0a05-3a61-4e29-a4c0-0ca8c70c53af`. Worker 1044 wrote this Lean proof
and Markdown; no proof code from other diagnostics was reused.

This unit proves only the four stated criteria. Power-chain stabilization
for compatible actions, the source's auxiliary `E_k` and `F_k` quotient
sequences, source finiteness comparisons and the final C.II localization
proposition remain separate obligations. Nor does this unit resolve the
source's finite-generation and Noetherian conventions for possibly nonunital
algebra actions.
