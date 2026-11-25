# Underlying supports and equality of translated global sections

This internal construction uses the published point-support,
analytic support-descent, global-germ and twisted-action interfaces. It assumes
no additional literature assertion.

Fix a complete ultrametric normed field `K`, a normed `K`-algebra field `L`,
an analytic space `X`, and `EtaleSite.PointAxioms L x` for every `L`-valued
point `x` of `X`. Coefficients are modules over a commutative ring in universe
`max u (v + 1) uL`. Underlying support means the direct image of point support
under `pointProjection`, as defined by `etaleUnderlyingSupport`.

A global germ is zero if its underlying point lies outside this image support:
a nonzero canonical germ would itself witness membership in the image.
Consequently, if the underlying supports of two global sheaf sections lie in
a set `W`, equality of their germs over `W` implies equality of all their
global germs. Outside `W`, both germs are zero. Assuming `pointProjection`
is surjective, the published `etaleGlobalGermMap_injective` then gives equality
of the sections.

The construction `etaleSupportedGlobalGermEmbedding` packages this conclusion.
Its domain consists of global sections whose underlying supports lie in `W`;
its codomain is the dependent family of stalk modules indexed by the
`L`-valued points projecting into `W`. It sends a section to those germs and is
injective under the same surjectivity assumption. It is an embedding of types;
no submodule structure is asserted.

For a group homomorphism `ρ : G →* Aut X` and a module presheaf on the twisted
étale site, `etaleUnderlyingSupport_actionRepresentation` identifies the
underlying support of the translate of a global section by `g` with the image
of its underlying support under the actual map `ρ g` on the analytic space.
The proof applies the published equivariance of point support, maps both sides
by `pointProjection`, and uses naturality of that projection. This result
requires neither surjectivity nor point lifting.

Finally, for a sheaf on the twisted étale site, suppose `W` contains the
underlying support of `s`, the map `ρ g` sends `W` into itself, and the global
germs of the translate and of `s` agree over `W`. The support-translation
identity puts the translated support in `W` as well. Applying the equality
criterion to the restricted étale sheaf proves that `g` fixes `s`, assuming
surjectivity of `pointProjection`.

The set `W` need not be open or compact. These constructions provide a
support-based equality criterion; they do not construct an open subgroup
fixing a compactly supported section or prove the cohomological comparison.
