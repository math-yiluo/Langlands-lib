# Smooth intersections with self-centralizing tori

This internal support unit identifies the fixed subgroup of normalized
conjugation by a commutative group with the inverse image of its ambient
centralizer, on all test schemes and their refinements.
If the acting subgroup is closed and equals its own centralizer, its actual
scheme-theoretic intersection with the normalized subgroup represents this
fixed subgroup.

`normalizedTorusIntersectionFixedModel` bundles that actual intersection and
its first projection as a closed representative of normalized fixedness. This
construction needs only a commutative acting group, its closed
self-centralizing inclusion, and a monomorphic normalized subgroup inclusion.

Over the spectrum of any commutative ring, an action of a split torus on a
smooth affine group has a smooth closed fixed-subgroup representative.
Consequently the actual intersection above is smooth when the acting subgroup
is a split torus. Affine open descent gives the result over any scheme when
the normalized subgroup is smooth and relatively affine. Étale splitting
extends it to relative tori.

In particular, `normal_subgroupIntersection_relativeMaximalTorus_smooth` proves
that over any scheme the intersection of a smooth relatively affine closed
normal subgroup of a reductive group with a closed relative torus having
maximal residue fibres is smooth over the base. All universes are arbitrary;
no noetherian or central-product hypothesis is added.

The proof rewrites fixedness by the ambient conjugation formula and cancels
the monomorphic inclusion. The intersection statement uses the published
pullback range formula. For smoothness, a split torus is reparametrized by its
diagonalizable model; the published arbitrary-ring diagonalizable
fixed-subgroup smoothness theorem applies. Uniqueness of subgroup
representatives transfers smoothness to the actual intersection. Arbitrary
base change preserves the intersection, normalization, closedness and the
self-centralizer equality. Smoothness is then checked on affine opens and
on the torus's étale splitting cover. The final corollary uses the published
self-centralization theorem for relative maximal tori; normality supplies
normalization by the torus.

This is derived internal content using the published normalized conjugation,
diagonalizable fixed-locus, and subgroup-intersection constructions. It does
not establish the relative-torus property or maximality of the
intersection, or the full derived-group correspondence. The
MaximalSelfCentralizingDescent and FppfLocality dependency pairs are used
unchanged.
