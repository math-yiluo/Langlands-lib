# Compatible-action power-chain stabilization: proofs

Author: Worker 691.

This module proves exactly
`Langlands.Algebra.CompatiblePowerStabilization.CompatiblePowerStabilizationStatements`
from the unchanged published statement module. It specializes the published
complex-linear power-chain proofs to actual compatible nonunital algebra
actions. The specialization is internal: Renard's Lemma (iv) is stated for
complex vector spaces, while the preceding definition extends stability
terminology to algebra-module endomorphisms.

The source correspondence is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.II,
definition and Lemma (iv), printed pages 276–278 / PDF pages 282–284,
registered as `renard-2026-representations-groupes-reductifs-padiques`.
The statement Markdown records the original, its older-edition errata and
the common-index prose typo. The proof uses the current Library's
`Langlands.LinearAlgebra.StableEndomorphismProofs`, authored by Worker 277,
rather than the source's auxiliary quotient sequences.

## Exact scope and declarations

All new declarations are in
`Langlands.Algebra.CompatiblePowerStabilization`. Each theorem below has its
closed published target as its complete type, with independent universe
parameters `uB uV`, in that order.

| Theorem | Published target |
| --- | --- |
| `powerUnderlyingMap` | `PowerUnderlyingMapStatement.{uB, uV}` |
| `powerKernelRangeMonotonicity` | `PowerKernelRangeMonotonicityStatement.{uB, uV}` |
| `adjacentStabilization` | `AdjacentStabilizationStatement.{uB, uV}` |
| `firstStabilizationIndex` | `FirstStabilizationIndexStatement.{uB, uV}` |
| `compatiblePowerStabilization` | `CompatiblePowerStabilizationStatements.{uB, uV}`, the conjunction in the published order |

The algebra `B : Type uB` is an arbitrary possibly noncommutative
`NonUnitalRing` with its compatible complex-module structure. The space
`V : Type uV` is an arbitrary complex vector space. The action
`ρ : B →ₙₐ[ℂ] Module.End ℂ V` and self-intertwiner
`f : LinearIntertwiner ρ ρ` are the actual published objects.
No hypotheses are added. In particular, zero actions, zero carriers and
arbitrary dimensions are included.

Every power is formed locally by installing
`CompatibleUnitization.module ρ`, taking the natural power of
`CompatibleUnitization.ofLinearIntertwiner f` in the actual unitized
endomorphism monoid, and applying
`CompatibleUnitization.toLinearIntertwiner`. No replacement power
constructor or global instance is introduced. All kernels, ranges, orders
and equalities in the conclusions are those of `CompatibleSubmodule ρ`.

## Implemented proof

`powerUnderlyingMap` proves
`(powers n).toLinearMap = f.toLinearMap ^ n` by induction on `n`.
At zero both maps are the identity, by the definitions of the actual
endomorphism monoids and the conversion. At the successor step,
`pow_succ` and `Module.End.mul_apply` reduce both sides to composition.
The conversion preserves the underlying function, so evaluation of the
induction hypothesis at `f v` proves equality at each vector `v`.
Thus exponent zero is included without eventual stability; its compatible
kernel is bottom and its compatible range is top.

`powerKernelRangeMonotonicity` applies the already published closed
complex-linear theorem of the same name in namespace
`Langlands.LinearAlgebra.StableEndomorphism` to `f.toLinearMap`.
The identities `LinearIntertwiner.ker_toSubmodule` and
`LinearIntertwiner.range_toSubmodule`, followed by the power-map identity,
identify the forgotten chains with the complex-linear chains.
`CompatibleSubmodule.toSubmodule_le_toSubmodule` reflects their two orders.
This proof uses no eventual-stability premise.

For each of the last two theorems, the proof first establishes, for all
natural `i,j`, that equality of the compatible kernels at `i,j` is
equivalent to equality of `LinearMap.ker (f.toLinearMap ^ i)` and
`LinearMap.ker (f.toLinearMap ^ j)`, and likewise for ranges.
These equivalences use `CompatibleSubmodule.toSubmodule_inj`, the actual
kernel/range forgetting identities and `powerUnderlyingMap`.

`adjacentStabilization` rewrites the published complex-linear closed
theorem through these equivalences. It therefore gives both the adjacent
kernel/range equivalence at each `k` and constancy of both chains at every
`m ≥ k` whenever either adjacent equality holds.
`firstStabilizationIndex` rewrites the published complex-linear
existential theorem through the same equivalences, including the negated
equalities before the first index. The witness is unchanged, as are its
constancy and minimality properties.

Both applications assume exactly the existing
`EventuallyStable f.toLinearMap`. This predicate retains its positive
power witness and the existing `Stable` predicate retains both square
equalities. The common first index ranges over all of `ℕ` and may be zero.
The complex-linear proof obtains it by taking the least adjacent kernel
equality, and uses eventual stability to obtain the adjacent range
equality and its persistence. No threshold, chain certificate,
finite-dimensionality, finite generation, Noetherianity, nondegeneracy
or splitting is assumed here.

Finally, `compatiblePowerStabilization` assembles the four proved
components in the exact aggregate order. The unchanged published target
and all its imported files are reused by Lean name.

## Boundaries

This module proves the power-chain aggregate only. The compatible
square/complement/exact-row stability criteria, the source's auxiliary
quotient spaces and sequences, source finiteness comparisons and the
final general C.II localization proposition remain separate obligations.
No assertion here discharges the whole-book formalization.
