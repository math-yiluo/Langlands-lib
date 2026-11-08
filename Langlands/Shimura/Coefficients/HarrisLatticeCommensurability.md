# Scalar comparisons in the original Harris coefficient module

Author: Worker 57. This is an internal deduction from the existing Harris
coefficient constructions and generic full-lattice scalar comparison. It
introduces no additional external-source assertion.

Fix the original algebra with involution, number field `L`, finite `L`-module
`W`, algebraic representation `ρ`, rational finite place `p`, and two compact
open levels `U` and `V`. No inclusion between these levels is required for the
main construction. Write

```text
R = ∏_{l above p} O_l,
B = L ⊗_ℚ ℚ_p,
H = B ⊗_L W,
Λ_U = harrisLattice ρ p U,  Λ_V = harrisLattice ρ p V.
```

All factors are the actual places and completions used in the imported
`HarrisLattice` and `HarrisSplitting` modules. Each local lattice is the original
compact-orbit-span lattice `algebraicCompactCoefficientLattice`; `Λ_U` and `Λ_V`
are their products transported into the original tensor module `H`. No lattice
or coefficient representation is replaced.

For each `l`, apply `latticeComparisonScalar` to the original local lattices at
`U` and `V`. The local valuation ring is a domain with fraction field the actual
completion. The generic theorem therefore supplies a nonzero `r_l` carrying
each of these lattices into the other. `harrisLatticeComparisonScalar` is the
element `r = (r_l)` of the original product ring `R`.

The component nonzero theorem records `r_l ≠ 0` for every place. The image
`s = harrisCoefficientIntegersMap L p r` is a unit in the original tensor
algebra `B`: the canonical ring equivalence sends it to the tuple of the
nonzero images of `r_l` in the completed fields, and a tuple of field elements
is a unit exactly when each component is nonzero. This does not assert that
`r` is a unit in the integral ring `R`.

The two `harrisProductLatticeComparisonScalar` theorems apply the local bounds
coordinatewise. The two `harrisLatticeComparisonScalar` theorems then transport
them through the original `R`-linear splitting. Consequently scalar
multiplication on the original `H` restricts to actual linear maps

```text
a = harrisLatticeScaledComparison ρ p U V     : Λ_U →ₗ[R] Λ_V,
b = harrisLatticeScaledComparisonBack ρ p U V : Λ_V →ₗ[R] Λ_U.
```

Both maps use the same chosen `r`. Their `coe` theorems say that the ambient
vector is multiplied by `r`. The `coe_tensor` theorems identify this action
with multiplication by `s` through the canonical integral embedding into
`B`. The coordinate theorem says that splitting the forward map is precisely
the generic scalar comparison in each original completed coefficient module.

The two composite theorems prove `b ∘ a = r² id` and `a ∘ b = r² id` on the
respective integral lattices, by ambient scalar associativity. Both maps are
injective: equality of images gives an equality after multiplication by `s`
in `H`, and multiplication by a unit of `B` is injective.

For any actual subgroup `T` contained in both level groups, the two action
constructions give morphisms between the restrictions of the unchanged
`harrisLatticeAction` representations to `T`. Their underlying maps are `a`
and `b`. The equivariance proofs use the original `B`-linear
`ρ.harrisAdelic p g`, restricted to `R`, so that this action commutes with the
scalar. These constructions apply in particular to the intersection of the
two level groups.

When `hVU : V.subgroup ≤ U.subgroup`, retain the original ambient inclusion
`i = harrisLatticeInclusion ρ p U V hVU`. The final three theorems identify
`b = r i` and prove the exact equations

```text
i ∘ a = r id_{Λ_U},    a ∘ i = r id_{Λ_V}.
```

These are equations involving the already constructed inclusion, rather than
inclusions newly defined from the comparison. They provide scalar
factorizations of the actual level map.

The ordered choice of `r` is not claimed symmetric or functorial in the
levels. The results concern integral lattices and their original actions.
Finite quotient cardinalities, tensor rationalization, adic systems and their
associated sheaves, rational independence, Hecke compatibility and the host
task's remaining geometric existence and canonical-model obligations remain
separate.
