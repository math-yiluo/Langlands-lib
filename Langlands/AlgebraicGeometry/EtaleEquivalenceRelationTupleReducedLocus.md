# Symmetric tuple threshold opens and reduced degree loci

This internal helper continues Stacks Lemma 68.8.3, Tag 0BBN, second proof
paragraph, registered as `stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
The paragraph proves that the unordered tuple cover becomes an isomorphism
over a reduced exact-degree stratum. The calculations here are derived from
the previous actual tuple quotients, saturated threshold opens, and field-point
matching. The actual affine quotients used in those helpers come from the
published specialization of Stacks Proposition 39.23.9, Tag 03BM, registered
as `stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`,
`03BM.txt`, statement and proof.

Assume the source map of `E` is separated and both its object and relation
schemes are affine. `tupleSymmetricThresholdOpen n k` is the open image, under
the ordered-to-symmetric quotient map, of the inverse image of object threshold
`k` under the ordered zeroth-coordinate projection. It is open because the
quotient map is étale and therefore open. These opens decrease in `k`, are the
whole symmetric tuple scheme when `k = n`, are quasi-compact, and vanish when
`k` is at least the uniform tuple-length bound. Quasi-compactness follows by
taking the compact preimage under the affine coordinate map and then the
continuous quotient image. `tupleSymmetricDegreeClosed n` is the closed
complement at `k = n + 1`. It is only a closed set; this declaration does not
choose a reduced scheme structure.

`tupleSymmetricCross_fieldPoint_endpoints_eq` proves equality of the two
unordered endpoint morphisms of a field-valued symmetric cross arrow whose
left endpoint avoids the next symmetric threshold. Pulling back the finite
étale surjective ordered-cross quotient map gives a cover of the field
spectrum. Its source is reduced by the published smooth-over-a-field
reducedness theorem. At every residue-field point of that source, the ordered
left zeroth-coordinate image avoids the next object threshold: membership
would put its symmetric endpoint in the forbidden open. The preceding maximal
tuple matching theorem therefore equates the unordered endpoints at each
residue-field point. The two morphisms on the reduced cover agree because
their affine target is separated and residue-field points detect such equality.
The covering map is an epimorphism, so the original endpoint morphisms agree.

`tupleSymmetricCross_endpoints_eq_of_reduced` applies this field-valued result
to every residue-field point of an arbitrary reduced test scheme and uses
the same separated-target equality criterion.

The last two declarations additionally assume that the original joint
relation map `prod.lift E.t E.s` is a closed immersion.
`tupleSymmetricCross_factors_unit_of_reduced` identifies each such cross arrow
from a reduced test scheme with the identity arrow on its left endpoint, using
joint endpoint extensionality and the two unit equations.
`tupleSymmetricCross_point_mem_unit_range` applies this factorization to the
residue-field point of an arbitrary point of the symmetric cross scheme.
If its left endpoint belongs to `tupleSymmetricDegreeClosed n`, the point
lies in the image of the unit morphism.

All statements allow an arbitrary universe `u`. These results prove endpoint
equality on reduced tests and the stated underlying unit-image containment.
They do not establish étaleness of symmetric endpoints, construct a
scheme-level stratum isomorphism, or prove the Noetherian first-level statement.
