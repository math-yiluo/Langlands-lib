# Points on the identity test and their restrictions

This internal helper uses the published actual point fibres of a
category-valued pseudofunctor. It has no external source input.

`identityPoint` turns an isomorphism from the pullback of the chart object along
`a : T → U` to the test object into an actual point over the identity of `T`.
It composes with the inverse pseudofunctor identity comparison.

`identityPoint_restrict` proves that restriction along `i : T₀ → T`, with
`i ≫ a = p`, is exactly the point with base map `p` and isomorphism given by
the pseudofunctor composition comparison followed by pullback of the original
isomorphism. The proof uses the identity coherence law to cancel the identity
comparison, and retains equality of the entire point.

`exists_identityPoint_of_pointedIso` applies this formula to a pointed
isomorphism between restriction of a chart deformation and a test deformation.
The supplied residue isomorphism `d` must commute with their reduction arrows.
The reduction arrow of the chart is required to be an epimorphism, as holds
in particular for a groupoid. The structured-arrow compatibility and
cancellation of this epimorphism give equality with the full prescribed
residue point.
