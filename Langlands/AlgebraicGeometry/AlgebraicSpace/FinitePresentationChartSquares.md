# Affine finite-presentation chart squares

Author: Worker 156.

This internal supporting module constructs fixed affine scheme charts for a
morphism of algebraic spaces over an affine scheme. It does not prove a
limit-descent theorem. Every statement retains an arbitrary scheme universe
`u`.

`exists_affine_etale_surjective_cover` takes a compact scheme, chooses a finite
subcover of its affine open cover, and forms the coproduct of those affine
schemes. The coproduct is affine because the family is finite. The induced
scheme map is etale by source locality and surjective by the covering property.

`exists_affine_finitePresentation_atlas` assumes an affine base and the
published `HasAtlasProperty (LocallyOfFinitePresentation ⊓ QuasiCompact)` for a
space. Its given atlas scheme is compact because its structure map is
quasi-compact and the base is affine. Refining that atlas by the preceding
etale surjective affine cover preserves etaleness, geometric surjectivity,
and local finite presentation of the structure map. This assertion requires
no quasi-separatedness of the space.

`relative_diagonal_property_chart_pairing` applies over any scheme base, with
no affineness assumptions. Given an actual represented pullback of two scheme
maps to a space, it transfers a represented property of the space's diagonal
to the scheme pairing into the product over the base. It first constructs the
abstract diagonal pullback square from the original pullback universal
property. The product comparison for scheme Yoneda then turns that square
into a represented square for the actual scheme product. Testing the given
relative diagonal property on this square gives the result. The property `P`
is arbitrary: neither monomorphism nor stability under base change nor
isomorphism invariance is assumed here.

`exists_affine_finitePresentation_chart_square` takes spaces `X` and `Y` with
the above finite-presentation atlas property, a quasi-separated target `Y`,
and any morphism `f : X ⟶ Y`. Over an affine base `S`, it produces schemes
`W` and `V` over `S`, both affine with locally finitely presented structure
maps, etale surjective charts `a : h_W ⟶ X` and `b : h_V ⟶ Y`, and an actual
map `φ : W ⟶ V` satisfying `a ≫ hom f = h(φ) ≫ b`.

Choose affine finite-presentation atlases `U ⟶ X` and `V ⟶ Y`. The represented
pullback `T = U ×_Y V` is etale and surjective over `U`, so its structure map
is locally of finite presentation. Its pairing into `U ×_S V` is
quasi-compact by the preceding diagonal lemma and quasi-separatedness of
`Y`. The product is affine, so `T` is compact. Refining `T` by another affine
finite-presentation atlas gives `W`; composing its source map with the map to
`X` and its other projection with the map to `V` gives the desired square.
There is no source quasi-separatedness hypothesis in this construction, and
no flatness, smoothness, or representability hypothesis on `f`.

The provenance is derived: these are consequences of the existing algebraic
space and represented-pullback definitions, the scheme-Yoneda product
comparison, quasi-compactness and Mathlib's finite affine open-cover and
scheme-coproduct APIs. No external mathematical assertion is assumed. The
published statement pairs and their import closures are unchanged.

`FinitePresentationChartSquaresStatement` names the final existence theorem
with all its scheme and space quantifiers as a proposition.
`finitePresentationChartSquares` proves that proposition using the same
implemented construction. This is a supporting statement and construction;
it does not assert limit descent.
