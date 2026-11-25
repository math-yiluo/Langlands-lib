# Diagonalizable one-cocycles in smooth connected unipotent groups

This is an internal derived module for the conjugacy of sections of
trigonalizable groups. Its main theorem says that every rational one-cocycle
of a diagonalizable group `D(Λ)` in a smooth connected unipotent group is a coboundary,
provided that `D(Λ)` is connected or the characteristic is zero. The dimension induction
uses the proved equivariant additive quotient in `DiagonalizableAdditiveQuotientProof`.

## Notation

`k` is a field in universe `u`. `𝔻 Λ` is the diagonalizable group
`Diagonalizable.groupScheme (CommRingCat.of k) Λ`, viewed as a group scheme, and `T₀` is the
base `Over.mk (𝟙 (Spec k))`. A cocycle `c : a.Cocycle T₀` is an actual morphism
`T₀ × 𝔻 Λ ⟶ U` with `c(h h') = c(h) · h(c(h'))`, and `a.coboundary v` is the cocycle
`h ↦ v · h(v)⁻¹`.

## Main theorem

`exists_coboundary`: let `k` be algebraically closed and `Λ` any abelian group in
universe `u`. Assume `hD : ConnectedSpace (𝔻 Λ).X.left ∨ CharZero k`. Let `U` be a
group scheme over `Spec k`
that is smooth, affine over the base and connected, with `IsUnipotent U`. Then for every
automorphic action `a` of `𝔻 Λ` on `U` and every cocycle `c : a.Cocycle T₀` there is a
rational point `v : T₀ ⟶ U.X` with `c = a.coboundary v`.

`exists_coboundary_of_smooth`: the same conclusion when `U` is smooth, affine over the base
and unipotent but not necessarily connected. The cocycle sends `(1, 1)` to the identity,
so by `range_subset_identitySet` it lands in the identity component `U⁰`. The action
restricts to `U⁰` (`AutomorphicAction.onIdentityComponent`), the cocycle lifts to `U⁰`, and
`exists_coboundary` applies there, because `U⁰` is unipotent as a closed subgroup of `U`.

## Helper results

- `isLinearVectorCoordinates_weightAction`: the standard coordinates of `𝔾ₐⁿ` are linear
  vector coordinates for `VectorGroup.weightAction χ`, for any commutative group scheme
  over `Spec k` and any character `χ`.
- `smooth_kernel`: the kernel of a homomorphism whose underlying scheme morphism is
  smooth is smooth over the base. It is the base change of that morphism along the unit
  section (`kernel_isPullback_scheme`).
- `isAffineHom_kernel`: the kernel is affine over the base when the source is affine over
  the base and the target is separated.
- `range_subset_identitySet`: let `k` be algebraically closed and `K` an affine, locally
  finite type unipotent group, and assume `hD`. If `z : T₀ × 𝔻 Λ ⟶ K` sends `(1, 1)` to
  the identity, the image of `z` lies in the identity component of `K`. If `𝔻 Λ` is
  connected, `z` restricted to `𝔻 Λ` has connected image containing the identity point
  (`IdentityComponent.range_subset_identitySet`). In characteristic zero, `K` itself is
  connected (`Unipotent.connectedSpace_of_isUnipotent_of_isAlgClosed`).
- `kernelι_comp_eq_one`: the kernel inclusion followed by the homomorphism is `1`.
- `not_isIso_identityComponentι_comp_kernelι`: for a surjective, locally finite type
  homomorphism `f : U ⟶ 𝔾ₐ` with smooth affine kernel, the inclusion of the identity
  component of the kernel into `U` is not an isomorphism. Otherwise the rational point of
  `U` lifting the coordinate `1` of `𝔾ₐ` (`SemisimpleIdentityComponent.exists_rationalPoint_lift`)
  would be killed by `f`, so `1 = 0` in `k`.
- `CoboundaryProperty Λ U`: the induction property, that `U` unipotent implies that
  every cocycle of every action of `𝔻 Λ` on `U` is a coboundary.
- `step`: the induction step, stated with an explicit induction hypothesis for all smooth
  connected affine groups of smaller `Lie.dimension`.

## Proof of the induction step

Fix `U`, `a` and `c`.

1. If `SubgroupFunctor.range (𝟙 U) = ⊥`, every point of `U` is the identity, so `c` and
   `a.coboundary 1` have the same underlying morphism.
2. Otherwise `diagonalizableAdditiveQuotient.diagonalizableUnipotentAdditiveQuotient`
   gives a character `χ` and a smooth surjective homomorphism `f : U ⟶ 𝔾ₐ` that is
   equivariant for `VectorGroup.weightAction χ`. The image cocycle `c.map f`
   (`AutomorphicAction.Cocycle.map`) is a cocycle in `𝔾ₐ` with linear action, so it is the
   coboundary of a rational point `w`, by
   `diagonalizableVectorOneCocycle.exists_coboundary` (any `Λ`).
3. Since `k` is algebraically closed and `f` is surjective and locally of finite type,
   `w = g ≫ f` for a rational point `g` of `U`. The twisted cocycle
   `c' = Cocycle.conjugate g⁻¹ c` has trivial image under `f`, so its underlying morphism
   factors through the kernel `K` of `f` (`mem_range_kernelι_iff`) as `z`.
4. `K` is smooth (`smooth_kernel`), affine, and unipotent as a closed subgroup of `U`
   (`unipotentClosedSubgroup`). Since `c'` sends `(1, 1)` to the identity,
   `range_subset_identitySet` puts the image of `z` in the identity component, and
   `FiniteEtaleImage.liftOver` factors `z` through `K⁰ = identityComponent K`. Let
   `n : K⁰ ⟶ U` be the composite inclusion.
5. The kernel is stable under `a`, because `f` is equivariant and the weight action fixes
   `1`. Hence `a` induces an action `aK` on `K⁰`
   (`AutomorphicAction.onRepresentedIdentityComponent`) for which `n` is equivariant,
   and `c'` lifts to an `aK`-cocycle `c'.lift n`.
6. `K⁰` is smooth, affine, connected and unipotent, and `n` is a closed immersion that is
   not an isomorphism. So `Lie.dimension K⁰ < Lie.dimension U`
   (`Lie.dimension_lt_of_proper_closedSubgroup`), and the induction hypothesis makes the
   lifted cocycle the coboundary of some `v`. Then `c' = a.coboundary (v ≫ n)`
   (`Cocycle.lift_map`, `Cocycle.map_coboundary`), and conjugating back by `g` gives
   `c = a.coboundary (g * (v ≫ n))` (`conjugate_conjugate_inv`, `conjugate_coboundary`).

`exists_coboundary` applies `smoothConnectedAffineGroup_lieDimension_induction` to
`CoboundaryProperty Λ` with this step.

## Scope

The hypothesis `hD` is where the proof needs connectedness: without it the twisted cocycle
need not land in the identity component of the kernel. For a disconnected `𝔻 Λ` in
characteristic `p` (for example a nontrivial finite constant group of order prime to `p`)
this module says nothing; that case is handled separately in the proof of the
conjugacy theorem.

## Provenance

Internal. The induction replaces the p-Lie algebra argument of SGA 3, Exp. XVII, 5.7
(proof of Théorème 5.1.1 ii) b)), which treats `μ_p` acting on `(𝔾ₐ)^r`. Here
the reduction to a linear action comes from the equivariant quotient of
`DiagonalizableUnipotentAdditiveQuotientStatement` instead.
