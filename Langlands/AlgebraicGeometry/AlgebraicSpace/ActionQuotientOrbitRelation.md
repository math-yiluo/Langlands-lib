# Points identified by an fppf action quotient are locally in one orbit

Author: Worker 193.

This helper module serves `ActionQuotientFinitenessProof`. Let `G` be a group scheme over a
scheme `S`, acting by `b : SchemeAction G Z` on a scheme `Z` over `S`. Let
`π : h_Z ⟶ Q` be an fppf sheaf quotient of the action (`IsFppfActionQuotient b π`). The
module shows that two `T`-points of `Z` with the same image in `Q` become translates of
each other by `T'`-points of `G` after restriction to the members `T' ⟶ T` of an fppf
covering sieve. It also shows that every point of `T` lies in the image of some member
of any fppf covering sieve of `T`.

## Declarations

All declarations are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.ActionQuotientOrbitRelation`.

- `orbitSetoid b T`: the relation on `T`-points of `Z` given by `x ~ y` if and only if
  `x = b.act g y` for some `g : T ⟶ G.X`. It is an equivalence relation by `act_one`,
  `act_mul` and inverses in the group `T ⟶ G.X`.
- `orbitSetoid_map`: restriction along `f : T' ⟶ T` preserves the relation (by the
  naturality of `b.act`).
- `orbitPresheaf b`: the presheaf of orbits `T ↦ Z(T)/G(T)` on schemes over `S`, with
  restriction maps induced from those of `h_Z`.
- `toOrbitPresheaf b : h_Z ⟶ orbitPresheaf b`: the quotient map.
- `orbitSieve b x y`: for `x y : T ⟶ Z`, the sieve of the morphisms `f : V ⟶ T` such that
  `f ≫ x = b.act g (f ≫ y)` for some `g : V ⟶ G.X`.
- `orbitSieve_mem`: if `π` is an fppf action quotient of `b` and `x`, `y` have the same
  image under `π` over `T`, then `orbitSieve b x y` is an fppf covering sieve of `T`.
- `exists_mem_range_of_mem`: for every fppf covering sieve `J` of `T` and every point
  `t` of `T`, some member `f : V ⟶ T` of `J` has `t` in the image of `f.left`.

## Proofs

`orbitSieve_mem`. Let `P` be the orbit presheaf and `ρ : h_Z ⟶ sheafify P` the quotient
map followed by the sheafification unit. For a point `(g, z)` of `G × Z`, the points
`b(g, z) = g.z` and `z` are in the same orbit, so `ρ` coequalizes the action map `b.hom`
and the projection `G × Z ⟶ Z`. Since `π` is the coequalizer of this pair among fppf
sheaves, `ρ` factors as `π ≫ φ`. Hence `x` and `y` have equal images in `sheafify P`.
The sheafification unit is locally injective
(`CategoryTheory.Presheaf.equalizerSieve_mem`): the sieve of the `f : V ⟶ T` on which the
classes of `f ≫ x` and `f ≫ y` agree in `P(V)` is covering. Agreement of classes in
`P(V)` means `f ≫ x = b.act g (f ≫ y)` for some `g`, so that sieve lies in
`orbitSieve b x y`, which is therefore covering.

`exists_mem_range_of_mem`. The fppf topology on schemes over `S` is induced from the fppf
topology on schemes (`GrothendieckTopology.mem_over_iff`). The fppf precoverage of
schemes contains isomorphisms, is stable under base change and composition, so a sieve
covers in the generated topology exactly when it contains a covering presieve of the
precoverage (`Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`). The fppf
coverings are jointly surjective, so a member of that presieve hits `t`. Regarded as a
morphism over `S`, it is a member of `J`.

## Provenance

Internal helper (provenance: derived). The statement's Markdown
(`ActionQuotientFinitenessStatement.md`, section "Derivation") gives the reason: "the
quotient presheaf is `T ↦ Z(T)/G(T)`", so the map `G × Z → Z ×_X Z` is surjective as a
map of fppf sheaves. This module states and proves the local form of that remark that the
proof uses. The names are internal.
