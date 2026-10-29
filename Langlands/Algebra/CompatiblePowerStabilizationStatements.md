# Power-chain stabilization for compatible nonunital algebra actions

This statement-only module gives an internal compatible-action specialization
of David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, Appendix C.II, Lemma (iv), printed pages 277–278 /
PDF pages 283–284. The preceding definition on printed276/PDF282 extends
stability terminology to algebra-module endomorphisms; the lemma itself is
written for complex vector spaces. The present targets express its power
chains in the Library's actual compatible-submodule lattice.

The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 reread PDF282–284 and visually inspected the diagrams on PDF283–284
while preparing the compatible-action adapter.

## Actual objects and scope

Each component is a closed definition returning `Prop`. It binds internally:

- `B : Type uB`, `[NonUnitalRing B] [Module ℂ B]`,
  `[IsScalarTower ℂ B B] [SMulCommClass ℂ B B]`;
- `V : Type uV`, `[AddCommGroup V] [Module ℂ V]`;
- an actual action `ρ : B →ₙₐ[ℂ] Module.End ℂ V`;
- an actual self-intertwiner `f : LinearIntertwiner ρ ρ`.

The universes `uB` and `uV` are independent, in that order. Multiplication
in `B` may be noncommutative and need not have a unit. Actions need not be
nondegenerate. Zero algebras, zero actions and the zero vector space are
included. There is no hypothesis of finite dimension, finite generation,
Noetherianity, nontriviality, countability or topology.

Only the public modules `CompatibleSubmodule`, `CompatibleUnitization` and
`StableEndomorphismStatements` are imported. In each target the same local
expression forms powers through the actual unitized endomorphism monoid:

```lean
letI := CompatibleUnitization.module ρ
let powers : ℕ → LinearIntertwiner ρ ρ := fun n =>
  CompatibleUnitization.toLinearIntertwiner
    ((CompatibleUnitization.ofLinearIntertwiner f) ^ n)
```

This uses the published correspondence with linear maps for the actual
unital action of `Unitization ℂ B`; it introduces no global power
constructor or instance. The maps remain intertwiners of the given original
action. Kernels and ranges below are `LinearIntertwiner.ker` and
`LinearIntertwiner.range`, with equality and order in
`CompatibleSubmodule ρ`.

Write `N_k = (powers k).ker` and `I_k = (powers k).range`.
All exponents and chain indices are natural numbers including zero.
The existing endomorphism monoid uses composition for multiplication and
the identity map for its unit, so exponent zero has `N_0 = ⊥` and `I_0 = ⊤`.
These are consequences of the power construction, not extra hypotheses
or additional theorem targets in this module.

## Exact declarations

All names are in
`Langlands.Algebra.CompatiblePowerStabilization`.

| Declaration | Exact content and provenance |
| --- | --- |
| `PowerUnderlyingMapStatement` | For every natural `n`, `(powers n).toLinearMap = f.toLinearMap ^ n`. This is an internal coherence assertion for the published unitization correspondence, derived from its identity and composition laws; it is not a separately numbered source assertion. |
| `PowerKernelRangeMonotonicityStatement` | `Monotone (fun k : ℕ => N_k) ∧ Antitone (fun k : ℕ => I_k)`. The monotonicity clause of Lemma (iv) is isolated without an eventual-stability premise, an elementary strengthening justified by composition of powers alone. |
| `AdjacentStabilizationStatement` | Assuming `EventuallyStable f.toLinearMap`, for every `k : ℕ`, `(N_k = N_(k+1) ↔ I_k = I_(k+1))`, and `(N_k = N_(k+1) ∨ I_k = I_(k+1)) → ∀ m : ℕ, k ≤ m → N_m = N_k ∧ I_m = I_k`. This is the adjacent-equality and persistence assertion of Lemma (iv) on actual compatible submodules. |
| `FirstStabilizationIndexStatement` | Under the same premise, there exists `k₀ : ℕ` such that `∀ m : ℕ, k₀ ≤ m → N_m = N_k₀ ∧ I_m = I_k₀`, and `∀ j : ℕ, j < k₀ → N_j ≠ N_(j+1) ∧ I_j ≠ I_(j+1)`. This records the source's common first stabilization index. |
| `CompatiblePowerStabilizationStatements` | The conjunction of the preceding four closed targets in table order, with universe parameters `uB uV`. This is internal packaging with no additional hypothesis or conclusion. |

The eventual-stability premise is precisely the existing
`Langlands.LinearAlgebra.StableEndomorphism.EventuallyStable` applied to
`f.toLinearMap`. It says that some **positive** power is stable, where
`Stable t` is the conjunction
`LinearMap.ker t = LinearMap.ker (t ^ 2)` and
`LinearMap.range t = LinearMap.range (t ^ 2)`.
No predicate is replaced or redefined here. Monotonicity and the underlying
map assertion have no eventual-stability premise.

The positive witness for eventual stability does not force the first
stabilization index to be positive. An invertible endomorphism has first
index zero; so does the zero space. The constancy clause at `k₀` includes
`m = k₀ + 1`, and the earlier adjacent inequalities therefore make `k₀`
the first index for both chains. No threshold or stabilization certificate
is supplied as an additional assumption.

## Source and errata correspondence

This unit specializes the vector-space assertions to compatible
self-intertwiners and actual invariant complex subspaces. It does not
identify all additive invariant subgroups with complex subspaces.
The original proof's final paragraph on printed278/PDF284 repeats `I_k`
when comparing the two chains. The targets follow the coherent common-index
assertion of Lemma (iv), as does the existing complex-linear statement
family, rather than reproducing that prose typo.

Worker 709 also reread PDF18–19 of the registered supplementary
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
Its correction to the old printed321 image formula uses `N_(k+2)`;
that correction is already present in the governing 2026 printed278/PDF284.
The older errata do not change these targets. No project errata note for
the governing registered source was present when this unit was prepared.
The 2026 edition governs all source numbering and correspondence.

## Status and separate obligations

These definitions state propositions and provide no substantive proofs of
the power-chain assertions. Compilation and complete declaration inspection
establish elaboration and quantifier structure; independent statement review
and Library publication remain required.

A later proof may transport the existing complex-linear assertions through
`CompatibleSubmodule.toSubmoduleHom` and its injectivity, after proving the
underlying-map identity. This is an implementation route, not a proof
included here, and requires checking the actual public proof API.

The compatible kernel/range-square and complement criteria, both exact-row
stability implications, the source's auxiliary quotient spaces and exact
sequences, source finite-generation and Noetherian comparisons, and the
final general C.II localization proposition remain separate obligations.
This module assumes none of those results or their desired conclusions.
