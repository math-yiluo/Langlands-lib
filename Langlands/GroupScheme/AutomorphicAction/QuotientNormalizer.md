# Normalizers induced by quotient actions

Worker 843.

These are internal formal consequences of the published flat-surjective local
lifting argument and automorphic-action laws, together with the
restriction-image preservation predicate.

`IntertwinesConjugation φ e x` is the predicate
`∀ g, φ(e(g)) = x φ(g) x⁻¹` for a group homomorphism `φ`, a source
automorphism `e`, and a target element `x`.

For a flat surjective group-scheme homomorphism `q : G ⟶ A` and an action of
`A` on `G` that restricts along `q` to conjugation,
`act_comp_eq_conjugation` proves that `q` intertwines the action with
conjugation by `A`. It checks equality after a local lift of the acting point,
where the claim is the homomorphism law for `q`. No rational-point lift is
assumed.

`mem_normalizer_map_of_map_pointAut_eq` is stated for an arbitrary group
homomorphism `φ : M →* N`, an automorphism `e` of `M`, and `x ∈ N`.
If `e` maps a subgroup `K` onto itself and `φ(e(g)) = x φ(g) x⁻¹`, then
`x` normalizes `φ(K)`. This applies to points over any test scheme by the
preceding quotient compatibility. The proof identifies the two composite
homomorphisms and uses functoriality of subgroup images.

`PreservesRestrictionImage.map_pointAut_range_eq` expresses the existing
existential preservation predicate as equality of the image subgroup under
the point automorphism. Its proof unpacks witnesses in both directions and
does not require restriction to be injective.
