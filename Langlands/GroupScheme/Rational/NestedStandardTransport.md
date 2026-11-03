# Nested standard subgroup transport

Author: Worker 12.

This internal helper supports the transport of cuspidality for associated
standard Levis. It develops the cocharacter argument directly from the published
definitions, without a representation theoretic classification input.

`Dynamic.orbit_add_zsmul_of_mem_centralizer` expands the pointwise cocharacter
sum and cancels the factor centralizing the point. The equality is an equality
of actual orbit morphisms on every test scheme.

`IsStandardCocharacter.exists_add_zsmul_of_nested` uses finiteness of the
simple roots to bound the negative pairings of a cocharacter. Adding a large
integer multiple of a cocharacter standard for the outer face makes every
pairing outside that face positive, while leaving the pairings on that face
unchanged.

`mem_standardUnipotent_conj_of_mem_standardLevi` applies these lemmas to a
standard cocharacter for a nested face, transported by the actual normalizing
point. Pairing invariance gives the required signs on the transported outer
face. The given `StandardCocharacterStatement` identifies the source and
adjusted target radicals with their dynamic unipotent subgroups. The target
Levi centralizes the cocharacter added in the adjustment, so the preceding
orbit equality identifies their identity limits. Dynamic functoriality under
an inner isomorphism completes the equivalence. Its scope is every test scheme.
This is an implementation lemma derived from the definitions and the displayed
structural hypotheses; it is not asserted as an additional external theorem.

All declarations lie in `Langlands.GroupScheme`. The orbit identity is
over an arbitrary base scheme `S`, commutative group scheme `T` and group
scheme `G`. The other two declarations are over an arbitrary field and an
affine group scheme. The nested cocharacter existence lemma requires an
explicit finite simple-root set and the stated zero and positive pairings;
it does not require reductivity. The final transport lemma additionally
takes connected reductivity, the maximal split torus, genericity,
`StandardCocharacterStatement`, finite simple roots, both nested inclusions,
both actual Weyl-image equalities and the outer-Levi membership. All these
are visible arguments; none is obtained by a new external assertion.

The integer chosen in the existence proof is `max b 0 + 1`, where `b` bounds
the finitely many negatives of the pairings of the given cocharacter.
Outside the outer face, the integral pairing of a standard cocharacter is
at least one, so this choice makes the sum positive. This argument also
works for an empty simple-root set.

The final proof reuses
`latticePairing_characterAut_cocharacterAut` and
`groupHom_cocharacterAut_comp` for the actual torus automorphism;
`standardLevi_le_dynamicCentralizer` for the point's centralizer membership;
and `Dynamic.unipotent_eq_comap_of_iso` for transport under the inner
isomorphism. `hStandard` supplies standard cocharacters and the required
identifications with dynamic unipotent subgroup functors.
`Dynamic.HasLimit` and the identity-limit condition agree because the two
orbit morphisms are equal. No rational-point topology or compact-limit
existence theorem is used. The final equivalence holds on every test
scheme, and the consumer specializes it to rational points.

The source assertion motivating the consumer is Aubert's 1996 erratum,
printed p. 4687/PDF p. 1, the association-invariance parenthesis following
the definition of `Alg({I})`. The source locator and fingerprint, and the
implemented representation argument, are recorded in
[RationalSupportAssociationInvariance](../../Representation/Aubert/General/RationalSupportAssociationInvariance.md).
The three lemmas here are internal deductions supporting that proof,
rather than separate claims attributed to that passage.
