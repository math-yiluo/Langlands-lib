# Unipotent radicals of normal connected subgroups: proof

Worker 4418.

This module proves `NormalUnipotentRadicalIntersectionStatement` (module
`Reductive.NormalUnipotentRadicalIntersectionStatement`) in every universe `u`,
with no hypotheses.

The statement: let `k : Type u` be an algebraically closed field, and let `G`
and `H` be smooth connected affine group schemes over `k`. Let `i : H ⟶ G` be a
closed subgroup inclusion whose full range functor is normal. Let
`r : U ⟶ G` and `s : V ⟶ H` be any supplied unipotent radicals. Then

```text
(SubgroupFunctor.range r).comap i = SubgroupFunctor.range s
```

as subgroup functors of `H`. The equality holds on every scheme over `k`,
including nonreduced ones.

The module only combines two theorems already in the Library. It adds no new
mathematics.

## Declaration

- `normalUnipotentRadicalIntersection :
  NormalUnipotentRadicalIntersectionStatement.{u}`: the unconditional proof.

## The proof

The proof term is

```text
normalUnipotentRadicalIntersection_of_fixedCenterContainingTorus
  fixedCenterContainingTorus
```

Both parts are Library theorems:

- `normalUnipotentRadicalIntersection_of_fixedCenterContainingTorus` (module
  `Reductive.NormalUnipotentRadicalIntersectionReduction`) derives the target
  from `FixedCenterContainingTorusStatement`.
- `fixedCenterContainingTorus` (module `Reductive.FixedCenterContainingTorusProof`)
  proves `FixedCenterContainingTorusStatement` unconditionally. That statement
  says: over an algebraically closed field, a split-torus action on a connected
  reductive group fixes a closed split torus containing the whole
  scheme-theoretic centre.

## How the reduction works

The following summarizes the Library reduction, for orientation.

1. The inclusion `V ⊆ i⁻¹(U)` is the Library theorem
   `IsUnipotentRadical.le_comap`. The radical of `H` is normal in `G`, so the
   greatest property of `r` applies to it.
2. For the reverse inclusion, quotient `H` by `V` and `G` by `V`, using the
   Library's actual radical quotients. The quotient `R = H/V` is connected
   reductive over the algebraically closed field. Kernel cancellation gives a
   closed normal inclusion `R ⟶ G/V`.
3. The schematic image `W` of `U` in `G/V` is a smooth connected normal
   unipotent closed subgroup.
4. The full intersection of `W` and `R` in `G/V` is central in `R`, by the
   Library's normal unipotent commutation theorem.
5. Only the trivial-action case of `FixedCenterContainingTorusStatement` is
   used. It gives a closed split torus in `R` that contains the centre of `R`.
   So the intersection lies in a split torus and in the unipotent group `W`.
   The Library theorem on split-torus/unipotent intersections then forces it to
   be trivial.
6. A test point of `H` that lands in `U` therefore maps to the identity of
   `R`. So it lies in the kernel of `H ⟶ R`, which is `V`.

The source of the statement is Conrad–Gabber–Prasad, *Pseudo-reductive
Groups*, second edition (2015), Proposition A.4.8, normal-subgroup case. The
implemented route uses the Library's centre-containing torus rather than the
source's multiplicative-type argument for the centre.

## Axioms

`lean_check` reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
