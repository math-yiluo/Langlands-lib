# Proof: torus-stable subgroups of connected unipotent groups are connected

Module `Langlands.GroupScheme.Unipotent.TorusStableSubgroupConnectedProof` proves

```lean
theorem Langlands.GroupScheme.torusStableUnipotentSubgroupConnected :
    TorusStableUnipotentSubgroupConnectedStatement.{u}
```

This is Milne, *Algebraic Groups* (2017), Corollary 16.25 (printed p.331; source ID
`milne-2017-algebraic-groups`). Let `U` be a connected unipotent affine group of finite type over
a field `k`, and let a torus `T` act on `U` by automorphisms (`a : AutomorphicAction T U`). Every
closed subgroup `h : H ⟶ U` that is stable under `T` and contains the fixed subgroup
`a.fixedSubgroup` is connected. So is every closed subgroup that represents `a.fixedSubgroup`.
The statement, its hypotheses and its relation to the source are explained in
[`TorusStableSubgroupConnectedStatement.md`](TorusStableSubgroupConnectedStatement.md).

## Route

Milne first reduces to `k` algebraically closed and replaces `U` and `H` by their reduced
subgroups. He then inducts on `dim U`, using a central `T`-stable subgroup `N ≅ 𝔾ₐ` (16.23) and
exact sequences of points. The Lean proof does the same two reductions but skips the induction.
Over an algebraically closed field it applies the published solvable case of the result,
`Langlands.GroupScheme.Torus.solvableFixedContainmentConnected`
(Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed., Proposition 2.1.12(2),(3)). That
result needs a smooth connected solvable affine ambient group, a split torus acting on it, and a
smooth closed stable subgroup containing the fixed subgroup. It concludes that the subgroup is
connected. After the reductions, the reduced subgroups of `U` and `H` meet these hypotheses.

## Helper lemmas (namespace `Langlands.GroupScheme.TorusStableUnipotentConnected`)

- `exists_lift_of_range_subset`: let `X` be a reduced scheme, `f : X ⟶ Y` a morphism and
  `g : Z ⟶ Y` a closed immersion with `Set.range f ⊆ Set.range g`. Then `f` factors through
  `g`. Proof: by `Scheme.Pullback.range_fst`, the projection `pullback.fst f g` is surjective.
  It is a closed immersion (the base change of `g`) and its target is reduced, so by
  `isIso_of_isClosedImmersion_of_surjective` it is an isomorphism. The lift is
  `inv (pullback.fst f g) ≫ pullback.snd f g`.
- `exists_overLift_of_range_subset`: the same lemma for morphisms in `Over B`. The lift is
  automatically a morphism over `B`.
- `exists_lift_of_points`: take `k` algebraically closed and `X` reduced and locally of finite
  type over `Spec k`. Suppose every `k`-point `x` of `X` has `x ≫ f` factoring through the closed
  immersion `g`. Then `f` factors through `g`. Proof: `X` is a Jacobson space
  (`LocallyOfFiniteType.jacobsonSpace`). Each closed point is the location of a `k`-point
  (`pointOfClosedPoint`), so the closed set `f ⁻¹' Set.range g` contains all closed points. By
  `closure_closedPoints` it is the whole space, and `exists_overLift_of_range_subset` applies.
- `exists_point_lift_of_mem_closure`: let `ψ : Z ⟶ U` be a closed immersion whose image is the
  closure of the locations of a set `Γ` of `k`-points of `U`. Then every point of `Γ` factors
  through `ψ`. This is `exists_overLift_of_range_subset` with `X = Spec k`.

## Core case: `connectedSpace_of_isAlgClosed`

Here `k` is algebraically closed. `U` is as in the statement. The acting group is a commutative
group scheme `S` with `IsSplitTorus S.toGrp`, acting by `c`. `h : H ⟶ U` is a closed subgroup
with `c.IsStable (SubgroupFunctor.range h)` and `c.fixedSubgroup ≤ SubgroupFunctor.range h`. The
proof has six steps.

1. **Reduced subgroup of `U`.** Apply `Langlands.GroupScheme.rationalPointClosureSubgroup` to
   all `k`-points of `U`. This gives a smooth closed subgroup `ζ : U' ⟶ U` whose image is the
   closure of the locations of all `k`-points. That closure is the whole of `U`, because closed
   points are locations of `k`-points and are dense (`closure_closedPoints`). So `ζ` is a
   homeomorphism onto `U`, and `U'` is connected. `U'` is affine and locally of finite type
   (composition with `U.X.hom`). It is unipotent by `Langlands.GroupScheme.unipotentClosedSubgroup`.
   It is solvable: `Langlands.GroupScheme.perfectFieldUnipotentSplit` shows that it is split
   unipotent (`k` is perfect), and `RelativeRoot.IsSplitUnipotent.isSolvableScheme` gives
   `RelativeRoot.IsSolvableScheme U'`.
2. **The action restricts to `U'`.** `S ⊗ U'` is smooth over `k` (`smooth_tensor`, with
   `IsSplitTorus.smooth`), so it is reduced
   (`Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field`). Since `ζ`
   is surjective, `exists_overLift_of_range_subset` lifts the action map
   `S ⊗ U' ⟶ U` through `ζ`. Hence `range ζ` is stable. Let
   `c' := c.onRepresentedSubgroup ζ`, so that `c'.act s x ≫ ζ = c.act s (x ≫ ζ)`
   (`onRepresentedSubgroup_act_comp`).
3. **Reduced subgroup of `H`.** Apply `rationalPointClosureSubgroup` to the set `Γ` of `k`-points
   of `U` that factor through `h`. This gives a smooth closed subgroup `ψ : H'' ⟶ U`. Its image
   equals the image of `h`: one inclusion holds because the image of `h` is closed. For the
   other, the closed points of `H` are dense, and their images are locations of points in `Γ`.
   `H''` is reduced, so `exists_overLift_of_range_subset` gives `θ : H'' ⟶ H` with
   `θ ≫ h = ψ`. `θ` is surjective on underlying spaces because `h` is injective and the two
   images agree. Similarly, `ψ` factors through `ζ`. `SubgroupFunctor.IsRepresentedBy.factorHom` then gives a
   homomorphism `j : H'' ⟶ U'` with `j ≫ ζ = ψ`, which is a closed immersion
   (`IsClosedImmersion.of_comp_isClosedImmersion`). By `exists_point_lift_of_mem_closure`, every
   point of `Γ` lifts to a `k`-point of `H''`.
4. **`H''` is stable under `c'`.** `S ⊗ H''` is smooth, hence reduced and locally of finite type.
   By `exists_lift_of_points`, it suffices to lift `c'.act` applied to a `k`-point `x` of
   `S ⊗ H''`. Composing with `ζ` turns it into `c.act` on the point `x ≫ snd ≫ ψ`. That point
   factors through `h` (via `θ`), so its image under `c.act` lies in `range h` by stability, and
   hence in `Γ`. By step 3 it lifts to `H''`. The lift then gives the stability of `range j`.
5. **The fixed subgroup of `c'` lies in `range j`.** `Langlands.GroupScheme.fieldFixedSubgroupRepresentability`
   (with `IsSplitTorus.isAffineHom`) represents `c'.fixedSubgroup` by a closed subgroup
   `φ : Φ ⟶ U'`. Write the split torus as `S.toGrp ≅ splitTorus I` and compose with the inverse of
   `Diagonalizable.splitIso` to get an isomorphism with the diagonalizable group of `I → ℤ`.
   Then `Diagonalizable.fixedSubgroup_smooth_of_actingIso` together with
   `Diagonalizable.FixedSmooth.fixedSubgroupSmooth` shows that `Φ` is smooth, hence reduced. By
   `SubgroupFunctor.range_le_of_algClosed_points`, it suffices to treat the `k`-points `x` of
   `U'` fixed by `c'`. For such `x`, `x ≫ ζ` is fixed by `c`, since
   `c.act s (x ≫ ζ) = c'.act s x ≫ ζ`. So `x ≫ ζ` lies in `range h` by hypothesis, hence in
   `Γ`. Its lift to `H''` from step 3 is a factorization of `x` through `j`, because `ζ` is a
   monomorphism.
6. **Conclusion.** `Torus.solvableFixedContainmentConnected` applies to `U'` (smooth, affine,
   connected, solvable), `S` with `c'`, and the subgroup functor `range j`. That functor is
   represented by the smooth closed subgroup `j`, is stable (step 4) and contains the fixed
   subgroup (step 5). So `H''` is connected, and `H` is the continuous surjective image of `H''`
   under `θ`, so it is connected too.

## General field: `TorusStableUnipotentConnected.connectedSpace`

This is the first part of the statement for an arbitrary field `k` and torus `T`. `IsTorus T`
gives a field `K` over `k` with `T_K` split. Let `E := AlgebraicClosure K` and
`b : Spec E ⟶ Spec k`. The steps are:

- `IsSplitTorus.baseChange_fieldTower` shows that `T_E` is split. `IsSplitTorus.isCommMonObj`
  makes `T_E` commutative, giving the commutative group scheme `S` the core case needs.
- `U_E` is locally of finite type and affine (base change of `U.X.hom`). It is connected
  (`Langlands.GroupScheme.connectedSpace_baseChange_of_connected`, using
  `ConnectedSpace U.X.left`) and
  unipotent (`unipotentFieldExtensionStatement`).
- The action is `a.baseChange b`. Stability carries over by `SubgroupFunctor.range_baseChangeHom`
  and `AutomorphicAction.IsStable.baseChange`. Containment of the fixed subgroup carries over by
  `range_baseChangeHom` and `AutomorphicAction.fixedSubgroup_baseChange`. Closedness carries
  over by `IsClosedSubgroup.baseChange`.
- The core case shows that `H_E` is connected. `b` is surjective (`fieldExtension_fpqc`), so its
  base change `pullback.fst H.X.hom b : H_E ⟶ H` is surjective. `H` is then a continuous image
  of a connected space, so it is connected.

## The theorem: `torusStableUnipotentSubgroupConnected`

Part 1 of the statement is `TorusStableUnipotentConnected.connectedSpace`. For part 2, let
`j : F ⟶ U` be a closed subgroup with `SubgroupFunctor.range j = a.fixedSubgroup`. Containment
of the fixed subgroup is immediate. Stability holds because a fixed point `g` satisfies
`a.act t g = g`: apply the fixedness condition with the identity refinement. So part 1 applies
to `j`.

No hypothesis beyond the statement is used. Only the axioms `propext`, `Classical.choice` and
`Quot.sound` appear.
