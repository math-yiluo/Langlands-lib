# Centralizers of points conjugate to points with toral centralizer

Worker 1296.

This helper module proves the torus part of
`Langlands.GroupScheme.RegularConjugateFiniteGaloisStatement`: the centralizer
of the rational point `x` is a torus over `K`. It is internal infrastructure
for that proof. The fields `K`, `L`, `E` are arbitrary fields in universe `u`,
with `K`-algebra structures on `L` and `E`; no finiteness, separability or
perfectness is assumed in this module. Centralizers are the all-test
centralizers `pointCentralizer` of `Langlands/GroupScheme/PointCentralizer.md`.

## Containment gives representation

`isRepresentedBy_pointCentralizer_of_le`: let `G` be a group scheme over
`Spec L`, `z` a section of `G`, `S` a torus and `j : S ⟶ G` a closed subgroup.
Assume that every point `c` of `G` on every test `Z` that commutes with the
pullback of `z` factors through `j`. Then `j` represents the centralizer of
`z`. The torus is commutative (`IsTorus.isCommMonObj`), so the assumed
containment becomes an equality by `range_eq_pointCentralizer`. A closed
subgroup has a monomorphic underlying morphism, so `j` is a monomorphism in
`Over (Spec L)`.

## The centralizer of `x` is a torus

`isTorus_of_isRepresentedBy_pointCentralizer`: let `G` be a group scheme over
`Spec K` and `z : Over.mk (Spec.map (algebraMap K L)) ⟶ G.X` a point over `L`.
Assume `S` is a torus over `L` and `j` represents the centralizer in `G_L` of
the section corresponding to `z`. Let `x` be a section of `G` over `K`,
`q : Spec E ⟶ Spec L` a morphism over `Spec K`, and
`g : Over.mk (Spec.map (algebraMap K E)) ⟶ G.X` with `g * x * g⁻¹ = q ≫ z`.
Then every group scheme `T` over `K` with a homomorphism `i : T ⟶ G`
representing the centralizer of `x` is a torus.

Proof.

1. The point `g` is re-indexed over the composite base `q.left ≫ (Spec K ← Spec L)`,
   which equals the structure morphism of `Spec E` by the triangle `Over.w q`.
   The conjugation identity is transported to this base.
2. `isRepresentedBy_pointCentralizer_baseChange_of_conj` (with `b` the
   structure morphism of `Spec L` and `c = q.left`) shows that the base change
   of the centralizer of `x` to `E` is represented by a homomorphism out of the
   base change `S_E` of `S` along `q.left`.
3. The base change of `T` to `E` also represents that subgroup functor
   (`IsRepresentedBy.baseChange`), so it is isomorphic to `S_E`
   (`IsRepresentedBy.isoOfIsRepresentedBy`).
4. Writing `q.left` as `Spec.map` of the induced algebra map `L → E`, the
   published `IsTorus.baseChange` shows that `S_E` is a torus over `E`; so is
   `T_E` by `IsTorus.of_iso`.
5. The published descent result `IsTorus.of_baseChange` concludes that `T` is a
   torus over `K`.
