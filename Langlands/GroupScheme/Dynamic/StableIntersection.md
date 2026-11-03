# Dynamic decompositions inside closed invariant subgroups

This internal helper is derived from the published definitions and proved
orbit-extension, closed-immersion and limit lemmas. It introduces no new
assertion from the literature. Its base scheme and universe are arbitrary.
All conclusions concern every test scheme, including nonreduced schemes.

A subgroup functor `F` is supplied with a closed group-scheme representative
and is invariant under conjugation by a cocharacter. A limit of a point of
`F` remains in `F`. The proof first applies stability at the universal
multiplicative-group parameter, showing that the orbit factors through the
representative. The published `AffineLine.exists_lift_of_unitInclusion`
then factors its affine-line extension through that closed subgroup.
Evaluation at zero gives the asserted membership. This argument needs no
separatedness assumption.

When the ambient group is separated, the dynamic decomposition restricts to
`F ∩ P(χ) = (F ∩ Z(χ))(F ∩ U(χ))`. The construction
`infParabolicLimitHom` restricts the existing limit homomorphism to
`F ∩ P(χ)` with values in `F ∩ Z(χ)`. Membership in `F` follows from the
closed invariant subgroup limit lemma above, and the group laws follow from
uniqueness of limits. This homomorphism is natural in every test scheme,
as proved by restricting the existing `limitHom_comp` theorem.

For a point `g`, its limit `l` belongs
to both `F` and `Z(χ)`. The point `l⁻¹g` belongs to both `F` and `U(χ)`,
and `g = l(l⁻¹g)`. The reverse inclusion follows from subgroup closure and
the existing inclusions of the centralizer and unipotent functors in the
parabolic functor. Both the exact pointwise-product predicate and a literal
set equality are provided. The two factors live over the original test
scheme; no field closure or covering replacement occurs.

This helper proves no parabolicity, reductivity, radical identification,
or existence of the supplied closed representative. Its invariance input
is an all-test property, as defined by `AutomorphicAction.IsStable`.
