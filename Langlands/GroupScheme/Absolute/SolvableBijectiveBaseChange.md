# Solvability along a base change by a field isomorphism

Author: Worker 1240.

Module `Langlands.GroupScheme.Absolute.SolvableBijectiveBaseChange`. It is derived
infrastructure for `Langlands.GroupScheme.ParabolicIntersectionGeometryStatement` (task
`7c372114-27b9-49eb-8f69-5b1df15fbbca`). The proof of that statement moves Borel subgroups
from `AlgebraicClosure k` to `AlgebraicClosure (AlgebraicClosure k)` along a bijective field
map. This module supplies the solvability part of that transport.

## Contents

- `IsSolvableGroupScheme.baseChange_of_bijective`. Let `K` and `K'` be fields in the same
  universe and `φ : K →+* K'` a bijective ring homomorphism. If `B` is a group scheme over
  `Spec K` with `IsSolvableGroupScheme B`, then its base change
  `(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj B` over `Spec K'` also
  satisfies `IsSolvableGroupScheme`.

`IsSolvableGroupScheme` (module `Langlands.GroupScheme.Absolute.Borel`) asks that the abstract
group of `AlgebraicClosure K`-points of the base change of `B` to `AlgebraicClosure K` be
solvable. The theorem needs no smoothness or finiteness hypothesis on `B`.

## Proof

Write `e = Spec.map (CommRingCat.ofHom φ)`.

1. `σ = RingEquiv.ofBijective φ hφ` is a ring isomorphism `K ≃+* K'`. Mathlib's
   `IsAlgClosure.equivOfEquiv` extends it to a ring isomorphism
   `ψ : AlgebraicClosure K ≃+* AlgebraicClosure K'`. By `equivOfEquiv_comp_algebraMap`,
   `ψ ∘ algebraMap K _ = algebraMap K' _ ∘ φ`.
2. In `Over (Spec K)` take two test objects. `T` is `Spec (AlgebraicClosure K)` with structure
   map `toAlgebraicClosure K`. `T'` is `Spec (AlgebraicClosure K')` with structure map
   `toAlgebraicClosure K' ≫ e`. `Over.isoMk` applied to `Spec.map ψ` gives an isomorphism
   `T' ≅ T`. The required square commutes by step 1, after `Spec.map_comp` and
   `CommRingCat.ofHom_comp`.
3. A chain of four group isomorphisms identifies the `AlgebraicClosure K'`-points of the
   iterated base change with the `AlgebraicClosure K`-points of the base change of `B`:
   - `baseChangePointsEquiv (toAlgebraicClosure K')` turns points of the iterated base change
     into `Over (Spec K')`-morphisms into the base change of `B` along `e`;
   - `baseChangePointsEquiv e` turns these into morphisms `T' ⟶ B.X`;
   - precomposition with the isomorphism of step 2 turns these into morphisms `T ⟶ B.X`. This
     is the group isomorphism `(yonedaGrp.obj B).mapIso`, inverted;
   - the inverse of `baseChangePointsEquiv (toAlgebraicClosure K)` gives the points of the
     base change of `B`.
4. The hypothesis says the last group is solvable. `Group.isSolvable_of_isSolvable_injective`,
   applied to the composite injective homomorphism, makes the first group solvable.

## Provenance

This module is derived, not a statement from a source. It is a formal transport of the
Library definition `IsSolvableGroupScheme` along a field isomorphism. No literature result
is used. The only external ingredient is Mathlib's `IsAlgClosure.equivOfEquiv`, which extends
an isomorphism of base fields to an isomorphism of their algebraic closures.
