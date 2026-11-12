# Standard families restricted to a canonical standard Levi

Worker 83 derives these comparisons for the chamber reduction task from the
published standard-cocharacter, dynamic Lie, standard-Levi family, and
connected-reductivity proofs. The indices are arbitrary subsets `J` and `K` of
the ambient simple relative roots, without a nesting condition.

`StandardLeviFamilyRestrictionStatement` quantifies over every field of
universe `u`, every connected reductive group `G`, every maximal split torus
`i : T → G`, a generic cocharacter `ν`, and two valid ambient simple-root
subsets `J` and `K`. For any connected reductive group `L` with a closed
inclusion `j : L → G` representing the actual standard Levi for `J`, it
asserts the following three equalities, with `iL` the actual factor of `i`:

- `P_L(J ∩ K) = j⁻¹ P_G(K)`;
- `L_L(J ∩ K) = j⁻¹ L_G(K)`;
- `U_L(J ∩ K) = j⁻¹ U_G(K)`.

These are equalities of subgroup functors on every relative scheme test,
including nonaffine tests. They include empty or equal index subsets and
possibly nonreduced relative root systems. The type supplies the affine
instances from connected reductivity; there is no splitness assumption on
`G`, and no global structural statement appears as an antecedent.
`standardLeviFamilyRestriction` proves exactly this proposition.

The ambient torus lifts to a represented standard Levi by
`standardLeviTorusFactor`. Its simple roots are `J`. An ambient standard
cocharacter for `K` is therefore standard in the Levi for `J ∩ K`: its pairing
is zero on the intersection, and positive on the remaining members of `J`.
The theorem `standardLeviStandardFamilies_inter` applies the published
standard-cocharacter comparison in both groups to this same cocharacter.
Closed-subgroup functoriality of the dynamic parabolic, centralizer, and
unipotent functors then gives all three exact inverse-image equalities on
every test scheme.

The canonical specialization obtains connected reductivity of
`Standard.leviScheme i ν J` from `standardLeviSplitComponentStatement`.
Affineness of that representative follows from its closed inclusion in `G`;
the local instance used to formulate its standard functors uses the published
`IsClosedSubgroup.isAffineHom_source` theorem.
The exact coordinate-line stabilizer corollary evaluates the parabolic
equality and uses `pointMatrix_restrict`. It retains unit scalars over the
global-section ring of every test scheme, rather than only field points.

The proof reuses `standardLeviStandardFamilies dynamicLie standardCocharacter`
only for its proved simple-root equality and genericity, rather than applying
its subset-family comparison outside its allowed `K ⊆ J` range. It then
chooses an ambient standard cocharacter for the given `K`, verifies the
intersection signs, and uses `standardCocharacter` for both reductive groups.
The final equalities are the published
`Dynamic.parabolic_eq_comap_of_isClosedSubgroup`,
`Dynamic.centralizer_eq_comap_of_isClosedSubgroup`, and
`Dynamic.unipotent_eq_comap_of_isClosedSubgroup`, after rewriting the
composite torus map with `standardLeviTorusFactor_comp`.

This is an internal derivation from the named Library proofs. No new claim is
attributed to external literature. It does not
prove an adelic factorization, membership of a Levi factor in its norm-one
subgroup, root-character bounds, or chamber coverage.

The instances introduced here have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and instance
scopes are unchanged.
