# Actual ring Weyl data on affine etale neighbourhoods

This internally derived construction packages the actual rank-one centralizer
and its supplied affine etale normalizer into `RingRootCell.WeylData` over the
neighbourhood's coordinate ring. It uses the existing actual centralizer cell,
coordinate-preserving base change, and prescribed-action affine unit-cell data.
It asserts no new correspondence with a particular literature statement.

The original ring `R` is any commutative local ring. The ambient group is
reductive and affine, its standard split torus is closed and fibrewise maximal,
and a fibrewise root datum is supplied. A cocharacter `mu` annihilates exactly
the chosen pair of opposite roots among the root labels. The two actual root
parametrizations lift into its relative cocharacter centralizer. The supplied
`AffineEtaleUnitCellData` has the original root-coroot reflection as its
prescribed action. There is no locality or reducedness hypothesis on the affine
coordinate ring.

The generic helpers first recover the algebra structure of the coordinate ring
from its actual affine projection by full faithfulness of `Spec`. Its algebra
base map is exactly the original projection. The identity comparison of affine
tests retains the global beta and delta coordinates. Inverting the pullback
point equivalence produces an actual section of the coefficient-ring group;
transporter base change supplies its prescribed action on the actual pullback
torus. A standard split-torus comparison expresses that action in the same
integral exponent coordinates.

`coroot_comp_root_over` and `reflectionIso_eq_exponentCommIso_over` use the
integral pairing equality from the residue field of the original local ring.
The root-coroot pairing is two, and projection extensionality identifies the
ring-calculus reflection with the root datum's exponent reflection over every
commutative coefficient ring. This argument does not require the coefficient
ring to be local. The converse cell-factorization transport follows by
injectivity of the group pullback-point equivalence and the existing exact
root-point and torus-point comparisons.

`affineEtaleWeylData` takes the normalizer to that actual pullback section and
the torus coordinate to the pullback of the supplied torus point, followed by
the standard split-torus isomorphism. The normalizer square lies in this torus:
the reflection is involutive, and a fibrewise maximal split torus in a reductive
group is its own centralizer. Closedness, fibrewise maximality and reductivity
are transported to the actual centralizer base change. The supplied cell
factorization transports back to the standard coordinates by the injective
point equivalence. Both scalar coordinates are the exact original global
sections, and their supplied unit proofs become the Weyl-data unit fields.
The three final projection lemmas record exact preservation of the normalizer,
beta and delta.

This module supplies ring Weyl data on the affine etale neighbourhood. The
normalization relation, descent to the original local ring, and the full local
Isomorphism Theorem are further obligations.
