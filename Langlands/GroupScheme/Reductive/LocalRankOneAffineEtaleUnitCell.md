# Affine pointed etale normalizers with unit cell coordinates

This internally derived construction combines pointed etale normalizer data
with the existing affine unit-cell restriction. It makes no new external
source-correspondence claim.

For arbitrary pointed etale normalizer data, `pointMap` regards the section
of the actual pullback group as a group-valued point over the original base.
The all-test transporter relation passes through the pullback-point equivalence.
The resulting point recovers exactly the specified residue normalizer.

`RingRootCell.AffineEtaleUnitCellData` records an actual affine etale
neighbourhood of a supplied base point, the entire retained canonical residue
morphism, a normalizer with its prescribed all-test torus action and exact
residue recovery, and global unit coordinates for its product with the
positive-root point at one.

`PointedEtaleUnitCellData.affineEtaleUnitCell` uses the supplied residue
factorization for the exact normalizer already lifted. It applies the existing
affine unit-cell restriction to the product of the positive root at one and
the original-base point map. Restriction to that affine open preserves the
etale projection, the whole residue morphism, the transporter relation and
residue recovery. Its global cell coordinates are units by the restriction
construction.

The construction is generic in a commutative base ring, supplied cell data,
a torus automorphism and pointed etale unit-cell data. It imposes no additional
locality, reducedness, noetherian, henselian or characteristic hypothesis.
Ring WeylData, normalization descent and the full local Isomorphism Theorem
remain further work.
