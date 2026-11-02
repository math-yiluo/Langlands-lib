# Closed diagonals of group presheaves with etale field atlases

Author: Worker 509.

This internal assembly works with an actual abelian-group presheaf on every
scheme over an arbitrary field, in universe `u`. It assumes that its diagonal is
representable by immersions and that it has an etale-surjective scheme atlas
whose structural map to the field is locally of finite type. Under precisely
these hypotheses the full presheaf diagonal is a closed immersion.

The implemented argument first uses the zero-graph pullback square to make the
zero section an immersion. Its represented pullback to the atlas is a scheme
`Z` immersed in the atlas scheme `U`. The other projection `Z → Spec k` is etale:
its represented pullback square is the base change of the given etale atlas
along zero. Fullness of the actual scheme Yoneda functor identifies that
projection with an actual scheme map. The slice identities identify it with the
composite `Z → U → Spec k`.

The atlas is locally Noetherian because it is locally of finite type over a
field. The published theorem for immersions from etale field schemes therefore
makes `Z → U` closed, without any quasi-compactness assumption. The published
atlas-descent theorem gives closedness of zero on every scheme pullback, and the
subtraction square gives closedness of the diagonal. The final construction is
the actual open complement of the identity's represented inverse image in `U`.

This is an internal derivation from the group-identity pullback squares,
field-immersion closedness and etale closed-immersion descent. It establishes no
atlas existence or initial immersed-diagonal theorem. In a Picard application,
those remain separate geometric inputs; this helper assumes neither Picard
representability nor any condition on global functions or on a chosen section.
