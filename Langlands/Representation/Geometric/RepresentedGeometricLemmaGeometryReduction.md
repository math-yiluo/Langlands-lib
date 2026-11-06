# Reduction of the represented geometric prerequisites to two structural statements

`RepresentedGeometricLemmaGeometryReductionStatement` is the implication

```
RepresentedParabolicDoubleCosetStatement.{u} →
  RepresentedParabolicLeviIntersectionStatement.{u} →
    RepresentedGeometricLemmaGeometryStatement.{u}
```

It goes from the two published structural propositions to the unchanged
published `RepresentedGeometricLemmaGeometryStatement`, the geometric part of
Renard VI.5.1. `representedGeometricLemmaGeometryReduction` proves this
implication. The work is in
`representedGeometricLemmaGeometry_of_doubleCoset_of_leviIntersection`.

The two inputs are:

- `RepresentedParabolicDoubleCosetStatement`. For parabolics `P ⊃ M` and
  `Q ⊃ L` of a connected reductive group `G` over a field, the double-coset
  space `P(k)\G(k)/Q(k)` of literal point images is finite. Every double coset
  also has a representative `z` such that some maximal split torus of `G`
  factors through `M` and through `zLz⁻¹`.
- `RepresentedParabolicLeviIntersectionStatement`. If the Levi subgroups `M`
  of `P` and `L` of `Q = L ⋉ U` contain a common maximal split torus, then
  `M ∩ Q`, `M ∩ L` and `M ∩ U` are represented by a parabolic `P'` of `M`, a
  rational Levi `M'` of `P'`, and a complementary geometric unipotent radical
  `N'`.

Both remain explicit hypotheses. This module proves neither of them, and it
does not claim an unconditional proof of the geometric prerequisites. The
original proposition and the datum `GeometricLemmaIntersectionDatum` are
unchanged.

## Proof

Fix the local field `k`, the group `G`, its canonical point topology, and the
parabolics `P = M ⋉ N` and `Q = L ⋉ U` with their hypotheses.

1. The double-coset statement gives finiteness of `P(k)\G(k)/Q(k)`, and for
   each double coset `a` a representative `z` of the double coset of
   `a.out`, hence of `a` (`DoubleCoset.out_eq'`). It also gives a maximal
   split torus `i : T ⟶ G` with factorizations `a' ≫ l ≫ p = i` through `M`
   and `b ≫ lQ ≫ q ≫ inn(z) = i` through `zLz⁻¹`. The published assembly
   `exists_enumerated_geometricLemmaIntersectionDatum` turns finiteness and
   one datum per double coset into the enumerated conclusion. So it remains
   to build a `GeometricLemmaIntersectionDatum` at `z`.
2. Apply the Levi-intersection statement to `P ⊃ M` and the conjugate
   parabolic `q ≫ inn(z)` (parabolic by `IsParabolicSubgroup.comp_iso`), with
   Levi `L` and radical `U`, and the torus `i`. This gives `P' ⊃ M'` and `N'`
   with the three identities `parabolic_eq`, `levi_eq` and `radical_eq`
   against `M ∩ zQz⁻¹`, `M ∩ zLz⁻¹` and `M ∩ zUz⁻¹`.
3. Apply it again to `Q ⊃ L` and the conjugate parabolic `p ≫ inn(z⁻¹)`, with
   Levi `M` and radical `N`, and the torus `i ≫ inn(z⁻¹)`. This torus is
   maximal split by `IsMaximalSplitTorus.comp_iso`. It factors through `L` by
   `b`, because `inn(z) ≫ inn(z⁻¹) = 𝟙` (`innerIso_inv_hom`), and through
   `z⁻¹Mz` by `a'`. This gives `Q' ⊃ L'` and `U'` with the primed identities.
4. Transporting `levi_eq'` along the ambient isomorphism `inn(z)` gives
   `range (lQ' ≫ q' ≫ lQ ≫ q ≫ inn(z)) = range (l ≫ p) ⊓ range (lQ ≫ q ≫ inn(z))`.
   This uses `range_comp_iso_eq_inf` and `inn(z⁻¹) ≫ inn(z) = 𝟙`. By
   `levi_eq` and commutativity of the infimum, this is `range (l' ≫ p' ≫ l ≫ p)`.
   Both composites are closed subgroups, hence monomorphisms over the base,
   so each represents this common subgroup functor.
   `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` gives the
   isomorphism `φ : L' ≅ M'` with `φ.hom ≫ l' ≫ p' ≫ l ≫ p = lQ' ≫ q' ≫ lQ ≫ q ≫ inn(z)`.
   This is the field `φ_comp`.
5. The field `e` is the map of `φ` on rational points, with inverse the map
   of `φ.inv`. It is continuous in both directions for the canonical Levi
   point topologies by `continuous_rationalPoints_map`. The field `e_apply`
   holds by definition.
6. `range i` lies in `range (l ≫ p)` and in `range (lQ ≫ q ≫ inn(z))`, so it
   lies in their infimum. By `levi_eq` that infimum is `range (l' ≫ p' ≫ l ≫ p)`.
   `SubgroupFunctor.exists_factor_of_range_le` gives `t` with
   `t ≫ l' ≫ p' ≫ l ≫ p = i`, so `isMaximalSplitTorus` holds.

The elementary helpers are:

- `range_comp_iso_eq_transport`: the range of a composite with an ambient
  isomorphism is the transported range.
- `range_comp_iso_eq_inf`: an equality of a range with an infimum of ranges
  is preserved by an ambient isomorphism.
- `subgroupFunctor_inf_comm` and `subgroupFunctor_le_inf`: commutativity of
  the infimum and its universal property, proved pointwise. `SubgroupFunctor`
  carries only a partial order and a binary infimum, not a lattice instance.
- `mono_hom_hom_of_isClosedSubgroup`: a closed subgroup inclusion is a
  monomorphism over the base.

## Provenance

This is an internal reduction. Its structure follows Renard V.4.7 (printed
pp.121–122 / PDF pp.127–128). For a representative `z` there, `M ∩ z·Q` is a
parabolic subgroup of `M` with Levi factor `M ∩ z·L` and unipotent radical
`M ∩ z·U`. Symmetrically, `z⁻¹·P ∩ L` is a parabolic subgroup of `L` with
Levi factor `z⁻¹·M ∩ L` and unipotent radical `z⁻¹·N ∩ L`. Renard proves both
assertions by conjugating to the standard case of V.4.6. The reduction
instead obtains each one from the Levi-intersection statement. Its
common-torus hypothesis is supplied by the double-coset statement. The two
Levi factors are conjugate by `z`, since `z⁻¹·(M ∩ z·L) = z⁻¹·M ∩ L`. The
datum records this as `φ`.

The two structural statements record the geometric content of V.4.5–V.4.7.
Their provenance is documented in their own Markdown files. The reduction
itself uses only the named transport, representability and assembly results
above. It works over the local field and topology of the target proposition.
The two inputs are stated over an arbitrary field without topology.
