# Naturality of determinant pullback

Let `X` and `Y` be schemes in universe `u`, let `M` and `N` be actual module
sheaves on `X`, and let `φ : M ≅ N`. Fix two families of open sets `T i` and
`S j`, each covering `X`, with actual free frames `e i` for `M` and `d j` for
`N`. Both families use the same finite index type `I : Type u`. The two chart
index types may differ. Let `q : Y ⟶ X` be any scheme morphism.

The imported `isoMap e d φ` is the determinant map between the module sheaves
glued from these frames. The imported `pullbackIso` compares actual sheaf
pullback with the determinant formed from the actual pulled-back frames.
`pullbackIso_naturality` proves the equality of actual isomorphisms

`q^*(det φ) ≪≫ pullbackIso d q =
pullbackIso e q ≪≫ det(q^*φ)`.

All covering proofs are supplied explicitly in Lean. The determinant on the
right uses `pullbackFrames e q` and `pullbackFrames d q`, and its module
isomorphism is the image of `φ` under `Scheme.Modules.pullback q`.

The proof starts with `frameGenerator_iso_expansion`, which expands each
source frame vector in the target frame using the actual coordinate matrix of
`φ`. Pulling back this equality of local morphisms and reading its coefficients
in the pulled-back target basis proves `isoMatrix_pullback`. Taking determinants
gives `isoUnit_pullback`, the compatibility of the generator coefficient with
the actual map `q.app V` on structure-sheaf sections.

`pullback_hom_ext_genSec_overlap` tests maps out of the pulled-back determinant
on generators over opens contained in an intersection `T i ⊓ S j`. Its proof
uses the actual pullback adjunction, sheaf separation on the intersection
cover, and the fact that every local section of the original determinant is a
scalar multiple of its chart generator. The abstract
`pullback_iso_square_section_images` and
`pullback_iso_square_eq_of_genSec_overlap` assemble a square from these local
images. The two determinant generator formulas and
`isoMap_pullback_generator_image` discharge their hypotheses; in particular,
the required naturality equality is proved rather than assumed.

`lineBundlePullbackNaturalityIso` regards the determinant of `q^*φ` as an
isomorphism of actual line bundles.
`lineBundlePullbackIso_naturality` gives the same square in the full subcategory
of line bundles, by equality of the underlying module maps.

This is derived from the Library's actual frame, isomorphism, local-morphism
pullback, and line-bundle constructions. It has no separate original-literature
claim. Its scope is finite constant rank with supplied frames and covers.
Variable-rank determinants, the canonical parabolic polarization and its
ampleness, and the unconditional relative parabolic representability theorem
remain separate obligations.
