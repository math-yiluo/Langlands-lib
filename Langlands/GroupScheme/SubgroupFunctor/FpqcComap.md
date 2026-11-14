# Fpqc inverse images reflect represented subgroup containment

This internally derived helper concerns an fpqc homomorphism `q : G ⟶ Q`
of group schemes over any scheme `S` in universe `u`. If `j : H ⟶ Q`
represents a subgroup by a monomorphism, then
`F.comap q ≤ (range j).comap q` is equivalent to `F ≤ range j`.
The subgroup functor `F` need not be representable. Both inclusions are
evaluated on every relative scheme test.

For reflection, the Lean proof pulls back `q` along an arbitrary test
point `x : T ⟶ Q.X`. The resulting fpqc cover `a : V ⟶ T` carries a
lift `z : V ⟶ G.X`. Restriction of membership in `F` and the assumed
inverse-image inclusion show that `a ≫ x` factors through `j`.
The published `SubgroupFunctor.mem_range_of_comp_mem_range` descends this
factorization through the monomorphism `j`, using the effective
epimorphism supplied by the fpqc cover. Preservation is the published
`SubgroupFunctor.comap_mono`.

`comap_le_iff_of_isRepresentedBy` rewrites an explicit representing
witness to this range formulation. This helper does not assert
reflection for arbitrary nonrepresentable target subfunctors.
