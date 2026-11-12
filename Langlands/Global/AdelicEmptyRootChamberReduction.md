# The empty-root case of actual adelic chamber reduction

This internal result proves the empty-simple-root base case of the chamber
factorization on the actual canonical subgroup schemes. It is derived from the
published `standardParabolicEndpoints` theorem and functoriality of actual
norm-one adelic points; it invokes no compactness or fundamental-set theorem.

`HasWeakChamberReduction` is the fixed-data weak-chamber factorization in the
host statement. For a number field, an affine group scheme, the specified torus
maps and cocharacter, and a specified subgroup `K` of the actual adelic group,
it asserts one positive threshold and the ordered equality

`image(n) * image(m) * positiveMap(a) * k = rational(q) * g`.

Here `g` and the canonical minimal-Levi point `m` are norm-one, `n` belongs to
the canonical standard unipotent source, `a` belongs to the intrinsic positive
subgroup of the specified derived torus and to the actual weak simple-root
chamber, and `k` belongs to the specified `K`. The definition supplies no
coverage theorem by itself.

For an actual connected reductive group, a maximal split torus and a generic
cocharacter, assume `simpleRelativeRoots i ν = ∅`. The full-index endpoint says
the standard Levi at the full simple-root set represents the whole group.
Rewriting that index as the empty set proves the canonical minimal Levi
represents the whole group as well. The represented-subgroup uniqueness
isomorphism `emptyRootStandardLeviIso` identifies it with `G`, and its forward
map is exactly the canonical inclusion `Standard.leviHom i ν ∅`.

`exists_normOne_standardLevi_lift_of_simpleRoots_empty` applies the inverse
morphism to an arbitrary ambient norm-one adelic point. The published
`mapNormOne` sends norm-one points to norm-one points, so its image is an actual
norm-one point of the canonical Levi. The inverse identity gives the required
ambient equality.

`hasWeakChamberReduction_of_simpleRoots_empty` assumes an actual
`IsSiegelAlgebraicSetup`, connected reductivity, and the empty simple-root set.
It proves the fixed-data chamber reduction for every subgroup `K`, and hence
for every supplied Iwasawa compact. Choose threshold `1`, the lifted Levi point,
and identities for the rational point, unipotent point, positive-torus point
and compact factor. Membership in the chamber is vacuous and `1 ∈ K` holds for
every subgroup. There is no local-finite-type premise beyond those implicit in
the supplied structural predicates, no splitting of `G`, and no compactness
assumption on `K` in this base-case theorem.

This result covers empty relative simple-root sets only. Uniform height bounds,
positive-rank induction and the general chamber theorem remain separate
obligations.
