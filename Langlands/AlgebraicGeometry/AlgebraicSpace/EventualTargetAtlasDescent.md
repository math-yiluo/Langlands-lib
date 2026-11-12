# Eventual target atlases and conditional property descent

This internal supporting result combines the actual fibre-product finiteness
theorem with the scheme-representation and target-atlas constructions. The model
uniqueness and effective-descent propositions remain explicit assumptions.

`FinitePresentationSchemeTargetAtlas f` packages an actual `SchemeTargetAtlas f`
with local finite presentation, quasi-compactness and quasi-separatedness of
both scheme structure maps. It asserts no property of the scheme map between
these corners.

## Eventual target atlas

`exists_finitePresentation_schemeTargetAtlas_of_modelUniqueness` concerns an
arbitrary small cofiltered diagram of affine schemes in universe `u`, its
limiting cone, and a morphism between quasi-separated spaces having a locally
finitely presented quasi-compact atlas at a stage. It assumes
`SpaceLimitModelUniqueness` and representability of the morphism after base change
to the limit. It produces a later stage and an actual `SchemeTargetAtlas` for
the base-changed morphism. The structural maps of both scheme corners are
locally of finite presentation, quasi-compact, and quasi-separated.

Choose an affine finite-presentation target atlas `V → Y` and form the actual
space `W = X ×_Y V`. Affineness supplies quasi-compactness and
quasi-separatedness of the structure map of `V`. The fibre-product theorem
supplies quasi-separatedness and a locally finitely presented quasi-compact
atlas for `W`. Its actual presheaf pullback square is the input to
`exists_schemeTargetAtlas_of_modelUniqueness`. That result recovers finiteness
of the represented limit scheme, descends a scheme model under model
uniqueness, and recovers its actual projection by the full Yoneda embedding.
Thus no finiteness of an auxiliary scheme or pullback space is an extra premise
of the theorem here.

## Conditional property descent

`spaceLimitRelativePropertyDescent_of_modelUniqueness` treats any scheme morphism
property stable under base change. It assumes model uniqueness,
`EtaleAtlasPropertyEffectivity P`, and `SchemeStructuralPropertyDescent P`, and
concludes the full `SpaceLimitPropertyDescends` equivalence for the corresponding
represented property of space morphisms. Original-stage representability and
the six scheme finiteness properties are not premises.

For the forward implication the relative property at the limit includes
representability there. The preceding theorem gives a later target-atlas
square. The direct-versus-iterated base-change comparison transfers the limit
property to the morphism at that later stage. The target-atlas limit theorem
then applies scheme property descent, followed by effective descent, to obtain
a further transition with the space property. A second base-change comparison
composes the transitions back to the original stage. The reverse implication
uses the published transition-to-cone property transport.

Four specializations use the proved scheme structural descent theorems for
closed immersions, affine morphisms, open immersions, and finite morphisms.
Each retains only model uniqueness and its corresponding effective-descent
proposition as additional inputs.

These are conditional supporting theorems. They do not prove model uniqueness
or effective descent, do not address properness or geometrically connected
fibres, and do not prove the unchanged eight-clause
`SpaceLimitPropertyDescentStatement`.
