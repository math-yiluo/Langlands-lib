# Local Zariski density through actual affine points

Author: Worker 135.

`Langlands.AlgebraicGeometry.PointTopology.rationalLocalDensity` proves
`RationalLocalDensityStatement.{u}` for every nonarchimedean local field
in arbitrary universe. The scheme is affine, integral, and smooth over
that field. The point set and topology are precisely the published
`RationalPoint` and `rationalPointTopology`.

This is an internal consequence of the neighbourhood-controlled
separation proof in `RingTheory.LocalFieldDensity.LocalSeparationProof`
and the published canonical affine point comparisons. No separate
assertion from external literature is claimed.

For an actual algebra point `p : AlgPoint K A K`, `algPointSpectrum p`
is the inverse image of the unique prime ideal of `K` under `p`'s
algebra map. It belongs to the spectrum basic open defined by `a`
exactly when `p a` is nonzero, since the maximal ideal of a field is
zero. These inverse images are open by continuity of evaluation and
the Hausdorff property of the normed field. The basic-open criterion
for continuity therefore proves `continuous_algPointSpectrum`.

The second helper treats a smooth domain algebra over a complete
nontrivially normed field, with independent field and algebra universes.
Fix a nonempty open set `U` of actual algebra points. A nonempty
spectrum basic open is defined by a nonzero element `a`. Choose any
point of `U`; openness makes `U` a neighbourhood of that point. Local
separation supplies a point still in `U` at which `a` is nonzero.
Thus the image of `U` meets every nonempty spectrum basic open and is
dense.

For the actual scheme, integrality gives a domain structure on its
global sections, and `smooth_affineCoordinateRing` gives smoothness of
the canonical coordinate algebra. The canonical complete nontrivially
normed field structure has exactly the given local-field topology.
`affineRationalPointHomeomorph` transfers the actual rational points,
with that topology, to the algebra points of the canonical coordinate
ring. `Scheme.homeoOfIso X.left.isoSpec` identifies the underlying
scheme space with its coordinate spectrum.

The equation `affineSchemePointEquiv_spec`, evaluated at the unique
field-spectrum point, proves that these comparisons carry the actual
map `p ↦ p.left (IsLocalRing.closedPoint F)` to `algPointSpectrum`.
Composing with the inverse spectrum homeomorphism proves continuity.
The algebra-point homeomorphism sends any nonempty analytic open set to
a nonempty evaluation-open set. Its spectrum image is dense by the
second helper; the inverse scheme homeomorphism preserves this density.
This proves exactly the second conclusion of the target.

The result gives local Zariski density, without asserting Haar nullness.
The connected-group integrality and Noetherian hypotheses, measure
argument, and actual dynamic open-cell complement comparison are
separate obligations.
