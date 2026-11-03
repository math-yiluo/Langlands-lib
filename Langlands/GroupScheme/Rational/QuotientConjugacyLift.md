# Lifting rational torus conjugacy through a scalar-linear vector kernel

This internal construction combines the proved equal-quotient torus-lift
conjugacy with a supplied rational lift of a quotient conjugator. All fields,
including finite and imperfect fields, and nonsplit tori are retained.

Let `n : N → G` be monic on the underlying relative schemes and suppose its
all-test range equals the range of the actual kernel inclusion of
`q : G → Q`. Assume `N` is affine. Let `i : H → G`, `i' : H' → G` be actual
homomorphisms with `IsTorus H`. As in `TorusVectorLiftConjugacy`, supply
coordinates identifying the points of `N` on every relative test with the
additive group of `Fin d → Γ(T, ⊤)`, and assume the actual kernel conjugation
action along the original `i` has the existing natural scalar-linear vector
coordinate property.

Suppose `x` is an actual rational point of `Q` and `f : H ≅ H'` satisfies
`(i ≫ q) ≫ inner(x) = f.hom ≫ (i' ≫ q)`. Supply an actual rational point
`g` of `G` mapping to precisely `x`.

`QuotientConjugacyLift.quotient_eq` proves equality of the quotient maps of
`i` and `(f.hom ≫ i') ≫ inner(g⁻¹)`. It uses the naturality of actual inner
automorphisms under `q` and cancels the inner automorphism of `x`.
`kernelCorrection` applies the existing actual torus-lift primitive to these
two maps, with the action along the original `i`. Thus the coordinate
hypothesis is needed only for this original action.

Write `v` for that actual rational point of `N`. The construction `conjugator`
is the actual rational point `g * (v ≫ n)` of `G`.
`conjugator_comp` proves that its image under `q` is exactly the originally
specified `x`: the kernel correction maps to the identity.
`conjugator_conjugates` proves
`i ≫ inner(g * (v ≫ n)) = f.hom ≫ i'`. The order is significant: composing
inner conjugation by `v ≫ n` and then by `g` gives inner conjugation by
`g * (v ≫ n)`. The inverse conjugation used in `quotient_eq` cancels with
the final conjugation by `g`. `subgroupConjugate` records this exact point and
the same supplied source isomorphism in the unchanged predicate.

Finally, `subgroupConjugate_iff_quotient_of_isTorus_vector_kernel` assumes
surjectivity of `q` on the actual rational sections. It proves that
`SubgroupConjugate i i'` is equivalent to
`SubgroupConjugate (i ≫ q) (i' ≫ q)`. The forward implication is the existing
postcomposition result. The reverse implication obtains `x`, `f` and their
equation from the quotient conjugacy, chooses a rational preimage `g` from
the supplied surjectivity, and applies the constructed correction.

The provenance is internal composition of established actual cocycle and
inner-automorphism constructions. This module does not assert that an
arbitrary quotient is surjective on rational points. It also does not
construct a vector kernel, coordinates, a quotient, or maximal tori in that
quotient. There is no maximality, smoothness, characteristic, field-cardinality
or splitness assumption here, and dimension zero is permitted. The full
solvable maximal-torus conjugacy theorem remains unproved.
