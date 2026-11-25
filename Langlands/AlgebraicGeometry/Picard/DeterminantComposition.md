# Composition coherence of determinant pullback

This module is an internal consequence of the Library's determinant frame
construction, its pullback comparison, and the canonical composition comparison
for actual module sheaves. It proves their composition law and lifts it to
actual line bundles. All schemes, covering indices and frame indices are in
universe `u`. A module sheaf `M` on `X` has supplied free frames `e` over opens
`T i`, with the same finite frame index type `I`; the hypothesis `hT` says
these opens cover `X`. Thus the frame rank is constant in this module.

For morphisms `f : Z ⟶ Y` and `g : Y ⟶ X`,
`pullbackCompositionIso` is the determinant map `isoMap` induced by the
canonical module isomorphism `(Scheme.Modules.pullbackComp f g).app M`.
Its source is the determinant glued from the successively pulled-back frames;
its target is the determinant glued from the frames pulled back by `f ≫ g`.
It is constructed from the actual module comparison, independently of the
determinant pullback isomorphisms.

`pullbackCompositionIso_generator_image` says that this determinant map takes
each generator of the successive pullback frame to the corresponding generator
of the composite pullback frame. It applies the imported determinant
generator-image criterion to `frameGenerator_pullback_comp`, which proves the
corresponding equality for every original frame vector.

`pullback_twice_hom_ext_genSec` proves extensionality for morphisms from the
successive pullback of the original determinant sheaf. Two applications of the
pullback adjunction reduce the claim to equality on the original local
generators. The imported determinant-generator extensionality uses the cover.

The section helpers `pullback_mapIso_hom_app_localSection` and
`hom_app_pullbackComp_localSection` express naturality of section pullback and
compatibility with the canonical module composition comparison, respectively.
`successive_iso_section_images` combines four supplied section-image equalities
for arbitrary module-sheaf isomorphisms. `pullback_twice_iso_eq_of_genSec`
uses double pullback extensionality to turn the resulting local equality into
an equality of isomorphisms.

`pullbackIso_composition` applies those helpers to the constructed comparisons.
It proves that pulling back `pullbackIso e g hT`, then applying the determinant
pullback comparison along `f`, then `pullbackCompositionIso`, equals the
canonical module pullback composition comparison on the original determinant
followed by `pullbackIso e (f ≫ g) hT`. The required section equalities are
the two successive determinant generator formulas, the generator formula for
`pullbackCompositionIso`, and the determinant generator formula for `f ≫ g`.

`lineBundlePullbackCompositionIso` lifts `pullbackCompositionIso` to the full
subcategory of actual locally free rank-one module sheaves.
`lineBundlePullbackIso_composition` proves the same equality for actual line
bundles and their canonical pullback composition comparison by forgetting to
module sheaves and applying `pullbackIso_composition`.

The provenance is derived from the imported Library APIs. This module proves the
constant-rank composition law. Naturality in module isomorphisms, compatibility
between different frame covers and variable rank are treated in
`DeterminantVariableNaturality`, `DeterminantVariableCoverPullback` and
`DeterminantVariableCoherence`; the construction and ampleness of the
parabolic polarization are not part of this module either. This is not a
proof of the parabolic representability statement
`RelativeParabolicSchemeStatement`, which the Library proves in
`Langlands.GroupScheme.RelativeLevi.ParabolicSchemeProof`.
