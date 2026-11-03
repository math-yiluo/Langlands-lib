# Actual Borel factorization over an algebraically closed field

This derived adapter transports the geometric Borel witness in
`IsParabolicSubgroup` back along the inverse of the map from the algebraic closure
of an algebraically closed field. It retains the original parabolic inclusion
and an actual factor map, hence its equality holds on every test scheme.

The natural double-pullback comparison lifts the standard pullback composition
and identity comparisons to group objects. Rational-point pullback along a base
isomorphism gives a multiplicative equivalence. This identifies the existing
solvability definition with solvability of rational points over an algebraically
closed field and proves its invariance under isomorphic change of base.

Borel maximality is transported by pulling any possible enlargement back along
the inverse base map. The original maximality makes that factor an isomorphism;
faithfully flat reflection then makes the original factor an isomorphism. The
remaining smoothness, connectedness and closed-immersion properties follow from
actual pullback and scheme isomorphisms. Finally naturality transports the exact
factor equation back to the original inclusion.

This is internal category-theoretic content derived from the Library definitions
in `Absolute/Borel` and the transport and base-change APIs. It does not assert
general field-extension preservation of Borels or parabolics, or establish
parabolic self-normalization. Worker 1346 supplied the adapter direction;
Worker 1297 implemented the construction and proof.

The entry `IsParabolicSubgroup.borelFactorizationOfIsAlgClosed` chooses data
`BorelFactorization i` from the proved existential
`IsParabolicSubgroup.exists_isBorelSubgroup_factor`. The data contains a group
scheme `B`, its Borel inclusion `inclusion : B ⟶ G`, the map
`factor : B ⟶ P`, and the exact law `factor ≫ i = inclusion`. Its `range_le`
lemma states containment on all test schemes, without affine or reducedness
restrictions. When `i` is closed, `factor_isBorel` promotes the factor to a Borel
subgroup of `P` using `IsBorelSubgroup.of_comp`.

All constructions and results are universe polymorphic. The factorization
assumes precisely `Field k`, `IsAlgClosed k` and `IsParabolicSubgroup i`; no
reductivity, conjugacy, dynamic subgroup, or self-normalizer premise is needed.
