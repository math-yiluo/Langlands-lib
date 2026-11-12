# Compact parabolic factorization from maximal compact Levi intersections

This is an internal derivation on actual rational-point groups. A continuous algebraic Levi retraction maps the compact preimage of a compact ambient subgroup to a compact subgroup of the Levi. Its section shows that the image contains the literal Levi preimage. If that preimage is maximal compact, the image equals it.

The implemented dynamic factorization uses the published algebraic limit homomorphism and its centralizer section. The closed parabolic inclusion makes the preimage compact for the canonical rational-point topologies. For an element of the compact subgroup in the parabolic, its limit therefore lies in the compact subgroup in the centralizer. Multiplying the original element on the left by the inverse limit gives an element of the unipotent kernel and of the compact subgroup. This proves the product in centralizer-then-unipotent order. The reverse containment uses the two published inclusions into the parabolic.

`dynamicCompactLeviRetraction` is the actual rational-points limit homomorphism restricted from the literal compact preimage in the represented parabolic to the literal compact preimage in the represented Levi. The preceding maximality argument supplies membership in the codomain, and the original homomorphism supplies the group laws.

`hasParabolicFactorization_of_maximal_compact_levis` specializes the argument to a connected reductive group over a nonarchimedean local field, a maximal split torus, and a generic cocharacter. The published standard-cocharacter theorem supplies a cocharacter representing each choice-free standard parabolic, Levi and unipotent subgroup. The published closed representatives identify their actual rational points and let the dynamic result apply. The conclusion is exactly `HasParabolicFactorization i ν K`, for the original subgroup `K`. Its hypotheses require compactness of `K` and compact-open maximality of every literal standard-Levi preimage.

The compact maximality hypothesis is explicit. This helper does not establish Levi inheritance, a simultaneous basis, or the final available-data statement.

The instances introduced here have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and instance
scopes are unchanged.
