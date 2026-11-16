# A Borel projection onto a supplied maximal torus

This internal supporting construction is derived from the Library's proved
étale-local dynamic presentation of a Borel pair, the dynamic relative Levi
theorem, relative unipotent-radical existence and uniqueness, and descent of
actual subgroup multiplication isomorphisms. It is not the semilocal
quasi-split inner-form theorem.

Over any scheme `S`, let `i : B → G` be a relative Borel in a reductive group
scheme. Suppose `T` is a commutative relative torus and `t : T → B` is a
homomorphism for which the ambient composite `t ≫ i` is a closed fibrewise
maximal torus. Then `t` is a relative Levi subgroup.

The proof chooses a global relative unipotent radical of `B`. The proved
Borel dynamic presentation supplies an étale cover on which the given torus
represents the dynamic centralizer. The dynamic theorem therefore makes the
given torus a local relative Levi. Uniqueness of relative radicals of that
dynamic parabolic identifies the local radical range with the pullback of
the global radical. Equality of these closed ranges transfers the actual
multiplication isomorphism to the global radical on each cover member;
étale descent then proves that `T × U → B` is an isomorphism.

For every relative Levi, `RelativeLevi.exists_fppfRetraction` constructs a
homomorphism to its actual Levi factor using the first coordinate of inverse
multiplication. The existing retraction theorem gives the section identity
and identifies its kernel on every relative test scheme with the radical
range. Smoothness of the radical makes the projection smooth, and the section
makes it surjective. Hence it is flat, surjective, and locally of finite
presentation with that full kernel, exactly `RelativeRoot.IsFppfQuotient`.

`RelativeLevi.FppfRetractionData l` stores the actual radical group scheme,
its inclusion, the projection, the relative-radical certificate, the
multiplication isomorphism, the section equation, smoothness, and the full
fppf quotient certificate. `RelativeLevi.fppfRetractionData` chooses this
data from the proved existence theorem; it assumes no extra projection
or decomposition.

The Borel specialization constructs a smooth fppf retraction `q : B → T`
with `t ≫ q = 𝟙 T`, together with the actual relative unipotent radical and
the multiplication isomorphism.
`IsRelativeBorelSubgroup.maximalTorusFppfRetractionData` packages this
construction as actual retraction data for the supplied `t`. No existence of the supplied maximal torus,
quotient of that torus, induced-torus presentation, vector-bundle series or
cohomological vanishing is asserted.
