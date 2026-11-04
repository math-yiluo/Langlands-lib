# Unipotent dimension bounds from dominant orbits and solvable stabilizers

Authors: Worker 1547 and Worker 317.

This internal helper combines codimension-one normality, the full action
kernel, a smooth connected normal closure, and vanishing of homomorphisms from
affine unipotent groups to tori. Its final two theorems retain
`AlgClosedReductiveNormalSolvableTorusStatement.{u}` as an explicit premise.
They advance the prescribed-Borel route to positive-root uniqueness.

## Actual stabilizer factors

Let `k : Type u` be any field, let `G`, `H`, and `B` be group schemes over
`Spec k`, and let `a` be an action of `G` on an actual scheme `X` over `k`.
Suppose `D : SmoothConnectedNormalClosure j` for `j : H → G`, the range
of `j` is contained in the full action kernel, and `b : B → G` is a
closed representative of the stabilizer of a supplied rational section
`x : Spec k → X`.

`SchemeAction.normalClosureStabilizerHom` constructs a group-scheme
homomorphism from `D.group` to `B`. The existing normal-closure stabilizer
lemma gives containment of `D.inclusion` in the range of `b` on every
scheme test. The representative's `factorHom` constructs the actual map.
`normalClosureStabilizerHom_comp` proves that its composite with `b`
is exactly `D.inclusion`.

`isClosedSubgroup_normalClosureStabilizerHom` proves that the factor is
a closed immersion: its composite with the closed immersion `b` is the
closed immersion `D.inclusion`. If `B` is solvable in the published
`IsSolvableGroupScheme` sense, then
`normalClosure_isSolvable_of_stabilizer` proves `D.group` solvable by
applying the published monomorphic-subgroup theorem to this factor.
These statements use the full all-refinement action kernel and all-test
stabilizer. Representability of the kernel is not assumed.

## Triviality under the structural input

`SchemeAction.range_eq_bot_of_unipotent_kernel_of_structural` works
over an algebraically closed field `k : Type u`. Its hypotheses are:

- `htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u}`;
- `IsPseudoReductive G`, which over an algebraically closed field means
  that `G` is smooth, affine and connected with trivial unipotent radical;
- a smooth affine connected group `H`, an underlying monomorphic
  homomorphism `j : H → G`, and `IsUnipotent H`;
- containment of `SubgroupFunctor.range j` in `a.kernel`;
- a supplied section `x` whose stabilizer is represented by a closed
  map `b : B → G`, with `IsSolvableGroupScheme B`.

The conclusion is `SubgroupFunctor.range j = ⊥` on all scheme tests.
The proof chooses the actual smooth geometrically connected affine normal
closure of `j`. Geometric connectedness gives connectedness over `k`.
The preceding stabilizer factor proves the closure solvable. Applying
`htorus` to its closed normal inclusion makes the closure a torus.
The published theorem
`IsUnipotent.range_eq_bot_of_range_le_isTorus` then kills the range
of `j`, using its containment in that torus. The centrality conclusion
of `htorus` is not needed.

## Dimension bound from a supplied dominant orbit

`SchemeAction.unipotent_dimension_le_one_of_dominant_orbit_of_structural`
works over an algebraically closed field in the same universe and assumes
the same `htorus`, `IsPseudoReductive G`, and closed solvable stabilizer
representative. It additionally takes:

- smooth affine connected group schemes `U` and `H`, with both
  `IsUnipotent U` and `IsUnipotent H`;
- a homomorphism `i : U → G` with monomorphic underlying slice map,
  and a closed subgroup homomorphism `j : H → U`;
- the actual Lie dimension inequality
  `Lie.dimension U ≤ Lie.dimension H + 1`;
- reduced `X`, locally of finite type and separated over `k`;
- a section `x` fixed by the action restricted along `j` and `i`,
  on every scheme test;
- a dominant quasi-compact actual orbit morphism for the `U`-action
  through `x`.

It proves the conjunction
`SubgroupFunctor.range j = ⊥`,
`Lie.dimension H = 0`, and `Lie.dimension U ≤ 1`.
The range in this conclusion is the subgroup functor of `U`.
Closedness of `i` is not required.

First, the published codimension-one theorem makes the range of `j`
normal in `U`. The dominant-orbit action theorem then places the range
of `j ≫ i` in the full kernel of the ambient `G`-action. The preceding
structural-input theorem makes this composite range trivial. Monicity
of `i` reflects that triviality to the range of `j` in `U`.

The auxiliary theorem
`Lie.dimension_eq_zero_of_range_eq_bot` applies to a homomorphism between
affine group schemes over any field with monomorphic underlying map.
Its trivial-range premise makes its represented tangent submodule zero;
the published represented-tangent finrank comparison identifies this with
the actual Lie dimension of its source. Applying it to `j` gives
`Lie.dimension H = 0`. The supplied dimension inequality then gives
`Lie.dimension U ≤ 1`.

## Provenance and remaining obligations

This is an internal derivation from the actual normal-closure and action
interfaces, `Unipotent.CodimensionOneNormality`,
`Torus.UnipotentHomNonsplit`, represented subgroup factorization, solvability
under monomorphisms, and the represented-tangent dimension comparison.
Worker 317 proposed this normality/kernel/torus step in the
prescribed-Borel route; Worker 1547 implemented the factors and composed
these proofs. No external source theorem is asserted in this helper.

The final results assume the normal-solvable-torus proposition and the
listed geometry. This module does not prove that structural proposition,
construct a Borel quotient or its dominant unipotent orbit, supply the
dimension inequality, or compare the final dimension bound with the
relative-root set. `RankOnePositiveRootUniquenessStatement` remains a
separate open proof obligation.
