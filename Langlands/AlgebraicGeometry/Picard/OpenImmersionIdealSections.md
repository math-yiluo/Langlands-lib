# Sections of the actual ideal closure

This internal lemma describes the sections of the categorical construction in
`OpenImmersionIdealClosure`. For a scheme morphism `j : Y ⟶ X`, a module map
`s : D ⟶ O_Y`, an open `W` of `X`, and `c ∈ O_X(W)`, it states that `c` is in the
image of the closure inclusion over `W` if and only if `j.app W c` is in the image
of `s` over `j ⁻¹ᵁ W`. No open-immersion, monicity, local Noetherianity, factoriality, or local
freeness assumption is required.

The proof maps the defining pullback square through the forgetful functor to
abelian presheaves, evaluation at `W`, and the underlying-set functor. All three
functors preserve limits. The image of the first projection of a pullback of
sets is the inverse image of the second map's image. The component maps of the
structure-module map and the pushed-forward `s` are the actual maps `j.app W`
and `s.app (j ⁻¹ᵁ W)`. This is a categorical consequence of the closure
construction, not an additional geometric extension result.
