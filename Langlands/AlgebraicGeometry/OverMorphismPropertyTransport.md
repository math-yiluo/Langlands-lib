# Transporting a morphism property across an isomorphism over the base

`prop_hom_of_overIso` is the unchanged proof of
`Langlands.AbelianScheme.OpenCoverStructure.prop_hom_of_iso` from
`AbelianSchemeStructureOfOpenCoverProof`, moved to a shared scheme module.
For a morphism property `Q` that respects isomorphisms, an isomorphism
`e : X ≅ Y` in `Over V` transfers `Q Y.hom` to `Q X.hom`. The proof uses the
commuting triangle and cancellation of the isomorphism `e.hom.left`.
The original abelian-scheme name remains a wrapper. The Picard test-reduction
wrapper uses the inverse isomorphism to express the other direction.
No hypotheses or mathematical conclusions change.
