# Actual fibre products of algebraic spaces

For arbitrary schemes `S`, arbitrary `AlgebraicSpace S` objects `X`, `Y`, `Z`,
and arbitrary maps `f : X ⟶ Z`, `g : Y ⟶ Z`, `fibreProduct f g` is the
fppf-sheaf pullback with its algebraic-space conditions proved. No definition
of algebraic space is modified. `FibreProduct.presheafIso` compares its full
underlying presheaf naturally to the categorical presheaf pullback;
`presheafIso_hom_fst` and `presheafIso_hom_snd` identify its projections.
`FibreProduct.isPullback` supplies the universal property in the actual category.

The construction implements Stacks Project, Algebraic Spaces (version ed88ff78),
Lemma 7.2 (Tag 04T9) and Lemma 7.3 (Tag 02X2), printed p.10, using the definition
on pp.8–9. Sheaf pullbacks have the corresponding presheaf pullback by Mathlib's
preservation theorem. The diagonal is representable by the general diagonal
lemmas in `PullbackDiagonals`: a pullback embeds into the product, and its relative
diagonal there is an isomorphism. Given actual scheme atlases `U → X`, `V → Y`,
the scheme `U ×_Z V` exists because every scheme map into `Z` is representable.
`atlasSchemeIso` gives its full Yoneda comparison. The atlas map is the induced
map of pullbacks. Étaleness and geometric surjectivity follow by factoring the
map of pullbacks into two base changes, exactly as in the cited proof.

Here geometric surjectivity and étaleness retain their existing meanings:
representability and the respective property on every represented scheme
projection. All constructions quantify over the base scheme and universe.
`HasPullback` and `HasPullbacks` instances make the construction available to
categorical limits APIs; `forgetToPresheaf S` preserves pullbacks. The presheaf
square itself is also exposed as `FibreProduct.isPullback_presheaf`.

`FibreProduct.isQuasiSeparated` proves quasi-separatedness of the constructed
space from that of `X` and `Y`; quasi-separatedness of `Z` is unnecessary for this
part. It applies the same categorical diagonal argument to the relative
quasi-compact morphism property. This means precisely the unchanged
`IsQuasiSeparated`: every represented scheme pullback of the presheaf diagonal
has quasi-compact projection. The finite-presentation atlas closure remains a
separate supporting obligation, not a conclusion of this module.
