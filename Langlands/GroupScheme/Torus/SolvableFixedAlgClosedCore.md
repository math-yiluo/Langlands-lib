# Connectedness of solvable invariant subgroups over an algebraically closed field

This unit proves the algebraically closed case of
`Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedStatement`. The field is
`k : Type u`, at an arbitrary universe `u`. All subgroup functors, fixed points and dynamic
functors are the published all-test ones.

## Main theorem

`Torus.connectedSpace_of_isAlgClosed` assumes the following, over an algebraically closed field
`k`:

* `H` is a group scheme over `Spec k` that is smooth, affine and connected, with
  `RelativeRoot.IsSolvableScheme H`: one derived-series bound works on every test scheme.
* `S` is a commutative group scheme with `IsSplitTorus S.toGrp`, acting on `H` by the
  automorphic action `c`.
* `F` is a `c`-stable subgroup functor of `H` with `c.fixedSubgroup ≤ F`.
* `q : C ⟶ H` represents `F`, `q` is a closed subgroup, and `C` is smooth.

Under these hypotheses `C.X.left` is connected. The hypotheses are explicit arguments in the
order of the statement, so the theorem gives the statement with `[IsAlgClosed k]` added.

## Proof

The route is not CGP's induction on dimension. It combines the published Lie–Kolchin
embedding with the opposite cell, the connectedness of dynamic centralizers and the Jacobson
property.

1. **A generic cocharacter.** `AutomorphicAction.exists_cocharacter_fixedSubgroup` gives a
   cocharacter `ν` of `S` whose restricted action `a := c.restrict (groupHom ν)` has the same
   fixed subgroup as `c`. So `a.fixedSubgroup ≤ F`, and `F` is `a`-stable
   (`IsStable.restrict`). Being a closed subgroup of the affine `H`, `C` is affine.
2. **Reduction to rational points.** `IdentityComponent.connectedSpace_of_forall_mem_range`
   shows that a smooth affine group over an algebraically closed field is connected once all of
   its rational points lie in the range of `identityComponentι`. The complement of the clopen
   identity component is open. If it were nonempty, it would contain a closed point, because the
   underlying space is Jacobson. That closed point is the location of a rational point
   (`RationalZariski.range_location`), which is impossible. The criterion
   `IdentityComponent.mem_range_identityComponentι_iff` identifies membership of a rational
   point with membership of its location in the identity component.
3. **A triangular model of `H ⋊ 𝔾_m`.** `SolvableFixedCore.rational_mem_identityComponent`
   proves the hypothesis of step 2. Let `A = a.semidirectProduct` and let `σ = a.semidirectInr`
   be its acting factor. `A` is smooth, affine and connected, with underlying scheme
   `H ×_k 𝔾_m`. `RelativeRoot.isSolvableScheme_semidirect`, together with
   `SolvableFixedCore.isSolvableScheme_gm` (commutative points), makes `A` solvable for all
   tests. Then `IsSolvableScheme.isSolvableGroupScheme` turns this into geometric solvability.
   The published Lie–Kolchin theorem `solvableTriangularEmbeddingStatement` gives a closed
   embedding `j` of `A` into the upper triangular group scheme. Let `ρ₀` be `j` followed by its
   inclusion into `GL_N`. Then every point of `A` maps to an upper triangular matrix. By
   `GeneralLinear.exists_triangular_innerIso_comp_eq_diagonalCocharacter` there is an upper
   triangular rational point `g` such that `σ ≫ ρ₀ ≫ inn(g)` is a diagonal cocharacter with
   weights `e`.
4. **The subgroup `C ⋊ 𝔾_m`.** Let `a' = a.onRepresentedSubgroup q hq hF` be the induced action
   on `C`, and `i'` the published closed inclusion
   `a.semidirectSubgroupInclusion F hF q hq : a'.semidirectProduct ⟶ A`. By
   `semidirectInr_comp_semidirectSubgroupInclusion`, `i'` carries the acting factor of
   `C ⋊ 𝔾_m` to `σ`. So `ρ = i' ≫ ρ₀ ≫ inn(g)` is a closed embedding of `C ⋊ 𝔾_m` with diagonal
   acting factor. The image of every point is `g M g⁻¹`, with `M` and `g` upper triangular.
5. **The cell decomposition.** Let `x` be a rational point of `C` and `y` its image in
   `C ⋊ 𝔾_m`. The matrix of `y` is upper triangular, so its cell minor is a unit
   (`isUnit_cellMinor_of_mem_blockParabolicSubgroup`).
   `Dynamic.exists_mem_parabolic_of_isUnit_cellMinor` then gives `p ∈ P(a'.semidirectInr)` with
   `y p⁻¹ ∈ U` for the inverse cocharacter. By `semidirect_unipotent_le_range` (the acting
   group `𝔾_m` is commutative), `y p⁻¹` is the image of a point `u₀` of `C`. By
   `semidirect_unipotent_eq_comap`, `u₀` is an identity-limit point of the restricted action of
   `a'`. The point `p₀ = u₀⁻¹ x` maps to `p`, and `semidirect_parabolic_eq_comap` makes `p₀`
   a point of `a'.parabolic`.
6. **Identity-limit points.** The published `AutomorphicAction.unipotent_le_identityComponent`
   puts `u₀` in the identity component of `C`.
7. **Parabolic points.** `AutomorphicAction.parabolic_le_identityComponent_of_centralizer_le`
   shows the following. If every fixed point of a `𝔾_m`-action lies in the identity component,
   then so does every point `p₀` of the parabolic functor. Let `l` be a limit of `p₀`. It is
   fixed (`HasLimit.mem_centralizer`), and `p₀ l⁻¹` has limit `1`
   (`HasLimit.mul`), so `p₀ = (p₀ l⁻¹) l` is a product of points of the identity component.
8. **Fixed points.** `SolvableFixedCore.centralizer_mem_identityComponent` proves the fixed-point
   hypothesis of step 7 for `a'`. Let `l` be a rational fixed point of `a'`. Then `q l` is fixed
   for `a` (`onRepresentedSubgroup_fixedSubgroup_eq_comap`). Hence its image in `A` lies in
   the centralizer `Z_A(σ)` (`semidirect_centralizer_eq_comap`). This centralizer is represented
   by the published affine scheme `Dynamic.Affine.centralizerScheme σ`, which is connected by
   the published theorem `dynamicConnected`, since `A` is smooth, affine and connected. By
   `centralizer_le_semidirectSubgroup`, `Z_A(σ)` lies in the semidirect subgroup of `F`. A
   centralizing point is a normal-factor point times an acting-factor point. The acting factor
   centralizes itself, so the normal-factor coordinate is `a`-fixed, hence in `F`. So the
   connected centralizer factors through `C ⋊ 𝔾_m`
   (`IsRepresentedBy.factorHom`). Its composite with the first semidirect coordinate is a map
   from a connected scheme to `C` sending the identity to the identity. By
   `IdentityComponent.range_subset_identitySet` its image lies in the identity component of
   `C`, and `l` is in this image.
9. **Conclusion.** `x = u₀ p₀` lies in the identity component of `C`.

## Relation to the source

The statement is the algebraically closed case of the derived statement
`Torus.SolvableFixedContainmentConnectedStatement`. That statement is derived from
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd edition (2015), Proposition 2.1.12(2),(3),
printed pp.59–61 (PDF pp.85–87), source `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`. As in the source,
a cocharacter with the same fixed points replaces the torus. Unlike the source, the cell
decomposition of 2.1.12(1),(2) is not proved by induction on the derived series. It is obtained
pointwise from a Lie–Kolchin triangular embedding, conjugated so that the cocharacter is
diagonal by an upper triangular matrix. Then every rational point lies in the opposite cell.
Connectedness of the centralizer is the published `dynamicConnected` for the connected group
`H ⋊ 𝔾_m`, rather than the source's argument through 2.1.12(3) and A.8.11.

The bridge from all-test solvability to the geometric solvability needed by Lie–Kolchin is the
published `IsSolvableScheme.isSolvableGroupScheme`, applied to `H ⋊ 𝔾_m`.
