# Intrinsic isotypic transport and conditional projector covariance

Worker 173 constructs an inverse to pullback on actual intertwiners and proves
transport and covariance laws for the existing compact-coefficient isotypic
subspaces. This is internal algebraic infrastructure derived from the published
`GroupTransport`, `Isotypic`, and `ConditionalProjection` modules. No original
literature theorem is asserted in this pair.

The groups `G` and `H` have independent universes `uG` and `uH`, and only group
and topology instances are assumed. The supplied map `e : H ≃ₜ* G` is a
continuous multiplicative equivalence. Its pullback convention is
`h ↦ ρ (e h)`, as in the published `SmoothRep.pullback`. The representative
carrier universe `uV` and the two ambient carrier universes `uW` and `uX` are
independent. No admissibility, finite dimension, finite length, compact-open
subgroup, Haar measure or topological-group hypothesis is added.

## Intertwiners and intrinsic submodules

`Langlands.SmoothRep.mapOfPullback` takes an actual intertwiner from
`ρ.comp e.toMonoidHom` to `σ.comp e.toMonoidHom` and returns an intertwiner
from `ρ` to `σ`. Its underlying linear map is unchanged, as recorded by
`mapOfPullback_toLinearMap`. Equivariance follows by evaluating the input
intertwining equation at `e.symm g` and cancelling `e (e.symm g)`.
The source and target vector spaces can have different universes.

The remaining declarations are in `Langlands.CompactCoefficientClass`.
For a class `c : CompactCoefficientClass G` and a smooth representation `A`
of `G`, `toSubmodule_isotypicSubrepresentation_pullback` proves

```
(isotypicSubrepresentation (pullbackEquiv e c)
  (SmoothRep.pullback e A)).toSubmodule =
(isotypicSubrepresentation c A).toSubmodule.
```

`toSubmodule_annihilatorSubrepresentation_pullback` proves the same formula
with `annihilatorSubrepresentation`. Both equalities compare actual submodules
of the unchanged ambient vector space; the acting groups may differ.

For each proof, quotient induction reduces `c` to an actual representative `D`.
The published single-representative formulas express the isotypic subspace as
the supremum of all intertwiner ranges from `D`, and the annihilator as the
infimum of all intertwiner kernels to `D`. The pulled-back representative is
the published `IrreducibleCompactCoefficientRep.pullback e D`. The maps
`SmoothRep.pullbackMap` and `SmoothRep.mapOfPullback` keep their linear ranges
and kernels. The universal properties of the supremum and infimum therefore
give both inclusions. No representative is selected globally.

## Conditional covariance and conjugacy

`isotypicProjectors_covariant` takes smooth representations `A` of `G` and `B`
of `H`, and actual equivariant endomorphisms `P` of `A` and `Q` of `B`. Its
hypotheses specify that both underlying linear maps are idempotent and that

- `P.range = isotypicSubrepresentation c A`;
- `P.ker = annihilatorSubrepresentation c A`;
- `Q.range = isotypicSubrepresentation (pullbackEquiv e c) B`;
- `Q.ker = annihilatorSubrepresentation (pullbackEquiv e c) B`.

For every actual intertwiner `f` from `SmoothRep.pullback e A` to `B`, and
every vector `v : A`, the conclusion is

\[
f(Pv)=Q(fv).
\]

The proof pulls back `P`, uses the two submodule transport equalities to
identify its range and kernel, and applies the published
`isotypicProjectors_natural` theorem for the group `H`. That theorem derives
naturality from intrinsic subspace preservation and uniqueness of an
idempotent with its specified range and kernel. Thus covariance also holds
when `f` is not invertible.

`isotypicProjectors_conjugate` assumes instead that `f` is an actual equivariant
linear equivalence from the pulled-back `A` to `B`. With the same idempotence
and range/kernel assumptions it proves the equality of linear maps

\[
Q=f\circ P\circ f^{-1}.
\]

The proof applies covariance at `f.symm v` and cancels `f (f.symm v)`.
This is applicable to outer conjugation whenever the relevant group
automorphism and equivariant linear equivalence have been supplied; inner
equivariance alone is not used as a substitute for that data.

These results construct no unconditional projectors. They neither assert
complementarity of the intrinsic pairs nor prove finite support of projector
families, compactness of their total image, or the product-Levi decomposition.
