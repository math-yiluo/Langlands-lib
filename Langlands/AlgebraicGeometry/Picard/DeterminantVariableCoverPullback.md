# Variable-rank determinant cover comparison and pullback

Let `M` be an actual module sheaf on a scheme `X` in universe `u`. The inputs
are two supplied covering frame families `e` and `d`, with possibly different
chart index types and independent finite ranks `n i` and `m j`. Their actual
free sheaves have indices `ULift (Fin (n i))` and `ULift (Fin (m j))`.
The morphism `q : Y ⟶ X` is arbitrary.

`isoUnit_refl_coverChange` identifies the mixed coefficient of the determinant
of the identity on `M` with the existing cover-comparison coefficient. The
section equivalence of the identity fixes the actual source basis, so both
mixed units are formed from the same target and source bases. The imported
mixed determinant construction handles unequal ranks on overlaps with trivial
section rings.

`hom_ext_genSec_overlap` determines sheaf morphisms from the determinant by
their values on generators on intersections of the two covers. Sheaf
separation, local scalar generation, and linearity prove the criterion.
The two generator-image formulas then give `isoMap_refl_coverChange`, an
equality of actual module-sheaf isomorphisms.

`pullbackIso_coverChange` specializes the imported variable-rank naturality
square to the identity on `M`. Substituting the identity identification on
both sides proves that pulling back the original cover comparison and then
using the second determinant pullback comparison equals first using the
first determinant pullback comparison and then comparing the two actual
pulled-back frame families.

`lineBundleIsoMap_refl_coverChange` lifts the identity identification to actual
line bundles. `lineBundlePullbackCoverChangeIso` is the direct comparison of
the two constructed pulled-back frame systems, and
`lineBundlePullbackIso_coverChange` proves their commuting square in the full
subcategory of locally free rank-one module sheaves. The latter proofs use
the equalities of underlying module maps.

The provenance is internal: this is the variable-rank adaptation of the
Library's `DeterminantCoverPullback`, derived from actual frame determinants,
cover comparisons, naturality, and their generator formulas. Frames and
coverage remain supplied. No finite-frame existence, parabolic Lie
polarization, ampleness, or parent representability theorem is asserted.
