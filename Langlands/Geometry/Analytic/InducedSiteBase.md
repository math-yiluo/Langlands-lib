# The base of an object over an induced space

Author: Worker 5254.

This module is a helper for the essential surjectivity part of Berkovich's
Example 1.2.1(i), `InducedSpace.QuasiEtaleSiteEquivalenceStatement`. The
example is in Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed p.3; it states the isomorphism of sites without an argument.
§1.1.2, printed p.2, of the same manuscript constructs the induced space
`X_{G/H}` as the disjoint union of copies of `X` indexed by `G/H` and gives its
universal property (extension of `H`-morphisms to `G`-morphisms).

The construction here is derived for this formalization from those two facts;
it is not an argument of the manuscript. Given a `G`-object `Y` with a
`G`-morphism `π : Y ⟶ X_{G/H}`, the open domain `π⁻¹(X_H)` of `Y` over the copy
of `X` indexed by the coset `H` is an `H`-object with a morphism to `X`; the
universal property then gives the comparison morphism from its induction to
`Y`. Namespace: `Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

Throughout, `G : Type z` is a group, `H` a subgroup, `X` an `H`-object and `Y`
a `G`-object of `LocalizedCategory` (Lean types `Action (LocalizedCategory …) H`
and `Action (LocalizedCategory …) G`), and `π : Y ⟶ inducedAction H X` a
morphism of `G`-objects. Points are elements of the underlying topological
space `localizedSpaceFunctor.obj`. `pointCoset H X p` (module
`InducedSpacePoints`) is the coset indexing the copy of `X` that contains the
point `p` of `X_{G/H}`; `baseCoset H` is the coset `H` itself and
`baseRep H ∈ H` its chosen representative `r`.

## Declarations

- `out_inv_smul c : c.out⁻¹ • c = baseCoset H`, for a coset `c ∈ G/H` and its
  chosen representative `c.out`.
- `unitHom_mem_copyDomain H X x`: the unit `unitHom H X : X → X_{G/H}` maps
  every point into the domain `copyDomain H X (baseCoset H)` of the copy
  indexed by `H` (module `InducedSiteFold`).
- `isIso_copyDomain_foldHom H X hP`: the morphism
  `domainι (copyDomain H X H) ≫ foldHom H X ≫ X.ρ r` from the domain of the copy
  indexed by `H` to `X` is an isomorphism; its inverse is the factorization of
  `unitHom H X` through that domain.
- `preimageDomain π c`: the open analytic domain of `Y` with carrier
  `π⁻¹(image of copy H X c)`; it is open because the image of a copy is open
  (`isOpen_range_copy_space`) and `π` is continuous on points.
- `mem_preimageDomain_iff π c y`: `y ∈ preimageDomain π c` if and only if
  `pointCoset H X (π y) = c`.
- `map_hom_ρ_apply π g y : π (g · y) = actionMap H X g (π y)` on points.
- `ρ_mem_preimageDomain π g y hy`: `g` maps `preimageDomain π c` into
  `preimageDomain π (g • c)`.
- `ρ_mem_preimageDomain_baseCoset π h`: for `h ∈ H`, `h` maps
  `preimageDomain π H` into itself, stated in the form required by
  `domainRestrict`.
- `isInvariantDomain_preimageDomain π`: `preimageDomain π H` is an invariant
  domain of the restriction of `Y` to `H`.
- `baseAction π`: the `H`-object `π⁻¹(X_H)`, i.e. `invariantDomainAction` of
  the restriction of `Y` to `H` on the domain `preimageDomain π H`.
- `baseInclusion π : baseAction π ⟶ (Action.res _ H.subtype).obj Y`: the
  inclusion of `π⁻¹(X_H)` into `Y`, as a morphism of `H`-objects.
- `baseHomV π`: the morphism `domainι ≫ π.hom ≫ foldHom H X ≫ X.ρ r` from
  `π⁻¹(X_H)` to `X` in `LocalizedCategory`: restrict `π`, fold the copies onto
  `X`, then act by `r`.

The remaining statements take a hypothesis
`hP : OpenPartitionCoproductStatement.{u, v, z}` (module
`OpenPartitionCoproductStatement`); they hold for every such `hP`, and the
statement itself is not proved here.

- `baseHomV_unitHom π hP : baseHomV π ≫ unitHom H X = domainι ≫ π.hom`.
- `baseHomV_comm π hP h`: `baseHomV π` commutes with the actions of `h ∈ H`.
- `baseActionHom π hP : baseAction π ⟶ X`: the `H`-morphism with underlying
  morphism `baseHomV π` (simp lemma `baseActionHom_hom`).
- `lift_baseInclusion_comp π hP`:
  `lift H (baseInclusion π) ≫ π = (inductionFunctor H).map (baseActionHom π hP)`.
  Here `lift H` (module `InducedAnalyticSpace`) is the inverse of the
  adjunction bijection `homEquiv H`, so
  `lift H (baseInclusion π) : Ind(π⁻¹(X_H)) ⟶ Y` is the comparison morphism,
  and the equation says it lies over `X_{G/H}`.

## Proof

`out_inv_smul`: `c = c.out • H` (`out_smul_baseCoset`), then cancel.

`isIso_copyDomain_foldHom`: the composite in one order is checked after the
monomorphism `domainι`, using `domainLift_comp`, `ρ(r)⁻¹ ≫ ρ(r) = 𝟙` and
`domainι_copyDomain_foldHom_copy`; in the other order it is `unitHom_foldHom`.

`mem_preimageDomain_iff` is `mem_range_copy_space_iff`. `map_hom_ρ_apply` is
the equivariance `π.comm g` applied to points. `ρ_mem_preimageDomain` combines
these with `pointCoset_actionMap`; for `h ∈ H`, `h • H = H`
(`smul_baseCoset`) gives the invariance.

`baseHomV_unitHom`: every point of `preimageDomain π H` maps by `π` into the
copy indexed by `H`, so `foldHom_copy_of_pointCoset` gives
`domainι ≫ π.hom ≫ foldHom ≫ copy H = domainι ≫ π.hom`; unfolding `unitHom`
and cancelling `ρ(r) ≫ ρ(r⁻¹)` gives the claim.

`baseHomV_comm`: `unitHom H X` is a monomorphism (`mono_unitHom`), so it
suffices to compare after composing with it. Both sides then reduce, by
`baseHomV_unitHom`, `unitHom_comm`, `domainRestrict_comp` and the equivariance
of `π`, to `domainι ≫ π.hom ≫ actionMap H X h`.

`lift_baseInclusion_comp`: apply the injective adjunction bijection
`homEquiv H`; by its naturality both sides correspond to `H`-morphisms
`π⁻¹(X_H) → Res X_{G/H}` whose underlying morphisms are `baseHomV π ≫ unitHom`
and `domainι ≫ π.hom`, which agree by `baseHomV_unitHom`.
