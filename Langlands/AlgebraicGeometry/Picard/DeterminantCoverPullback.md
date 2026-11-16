# Determinant cover comparison and pullback

This derived module proves that determinant cover comparison commutes with actual
module-sheaf pullback, and lifts the comparison and equality to actual line
bundles. The inputs are two supplied covering frame families `e` and `d` for
the same module sheaf `M` on a scheme `X`. Both use the same finite index type
`I`, so the rank is constant. Schemes, chart indices, and `I` lie in universe
`u`. The morphism `q : Y ⟶ X` is arbitrary.

`isoUnit_refl_coverChange` identifies the local coefficient of the determinant
map of the identity module isomorphism with the mixed determinant coefficient
of cover comparison. The identity acts trivially on frame vectors, so both
coefficients are the determinant of the same coordinate matrix.

`hom_ext_genSec_overlap` tests maps out of the determinant on every intersection
of one chart from each cover. These intersections cover `X`; on each
subordinate open, the determinant generator spans all sections. Sheaf
separation and linearity then give equality of the module-sheaf maps.

`isoMap_refl_coverChange` uses this criterion and the two generator-image
formulas to identify the actual determinant of the identity with the existing
cover-change isomorphism. `pullbackIso_coverChange` specializes determinant
pullback naturality to the identity module isomorphism and substitutes this
identification on both sides. The equality states that pulling back the
original cover comparison and then applying the second determinant pullback
comparison equals applying the first determinant pullback comparison and then
the cover comparison of the two actual pulled-back frame families.

`lineBundleIsoMap_refl_coverChange` lifts the identity identification to line
bundles. `lineBundlePullbackCoverChangeIso` is the cover comparison constructed
directly from the two actual pulled-back frame systems.
`lineBundlePullbackIso_coverChange` proves the same commuting square for these
line bundles. The proofs use the faithful inclusion of line bundles as the full
subcategory of locally free rank-one module sheaves.

The provenance is internal: these are consequences of the imported actual
frame determinants, cover comparisons, generator formulas, and determinant
pullback naturality. No original-literature theorem is transcribed here.
Variable rank, the canonical parabolic Lie determinant polarization, its
ampleness, and the parent parabolic representability theorem remain open.
