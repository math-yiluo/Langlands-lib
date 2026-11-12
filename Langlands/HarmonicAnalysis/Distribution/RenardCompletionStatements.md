# Renard II.3.13: right-essentially-compact distributions and completed H(G)

This unit states the Theorem and both comparison formulas in its proof in
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, II.3.13, printed p.55 / PDF p.61. It uses any Hausdorff
locally compact totally disconnected topological group, in an arbitrary
universe, its Borel structure and any left Haar measure. It adds no
countability or unimodularity restriction.

The namespace is
`Langlands.HarmonicAnalysis.Distribution.RenardCompletion`.
The objects on the two sides are the published submodule
`Distribution.rightEssentiallyCompact μ` of the full algebraic dual and
the published actual compatible-family carrier
`Langlands.Algebra.IdempotentedRingRightLimit (HeckeAlgebra μ)`.
The latter consists of families in the original Haar Hecke algebra whose
coordinate at each idempotent `e` lies in the actual right image `Ae`,
with the right-image transition relations. It is not a supplied abstract
completion.

`ComparisonSpecification μ hA p E` characterizes the additive equivalence
`E` by the distribution identity
`heckeDistribution μ ((E T).val e) = T * e` for **every** actual Hecke
idempotent `e`. This is the source's forward formula. Coordinates are
not restricted to the compact-open normalized idempotents.

The specification requires coordinatewise complex scalar compatibility
and preservation of the given bilinear product `p`, using the published
`IdempotentedRingRightLimit.product hA`. That product is precisely the
multiplication in the existing named `IdempotentedRingRightLimit.ring hA`.
It also sends the actual Dirac identity to the published unit family and
extends the canonical map `h ↦ (e ↦ h * e)` on the actual Hecke density
range. Thus it asserts a complex-algebra isomorphism without installing
an unproved algebra instance on distributions, or introducing a parallel
scalar-module structure on the family carrier.

The inverse evaluation formula is asserted for every family `a`, test `f`
and actual idempotent `e` such that the scalar convolution `f * e = f`
and the inverted distribution of `e` equals `e`. It says
`(E.symm a)(f) = heckeDistribution μ (a.val e) f`. The scalar convolution
is the published `rightConvolveTest f (heckeDistribution μ e)`, matching
the source's distribution/test convention. For a general Hecke density,
this must not be replaced by left-Haar convolution against its bare
function; those formulas can differ on nonunimodular groups.
Compact-open normalized idempotents provide the required choices, are
fixed by inversion and fix every test after sufficient refinement, as
covered by the separate Hecke statement units.

`Statements` existentially supplies the Hecke idempotentedness proof,
the product satisfying `RenardEssentialProducts.RightProductSpecification`
and the uniquely characterized comparison. It does not assume these
mathematical obligations as hypotheses. The internal uniqueness
formulation makes the identification explicit; the coordinate formula
and faithfulness of the Haar density determine it.

There is no proof of `Statements` here. The product existence target and
the categorical-center corollary remain separate statement units.
