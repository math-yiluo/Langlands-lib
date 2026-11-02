# Block determinant basis

This module derives the block-Levi character description from
the GL determinant classification, in the setting of rational characters in
Renard (2026), V.2.2 and V.3.6, printed pp.105 and 111, and Waldspurger (2003),
I.1, printed pp.238–239.

The actual published block Levi scheme has points identified naturally with
tuples of invertible diagonal blocks. The resulting projections and inclusions
are actual morphisms of group schemes, constructed from these natural maps on
points. Each point is the ordered product of the points with only one nonidentity
block. Pullback of the determinant along the corresponding projection is
exactly the block determinant character from the published rational-character definitions.

Restricting a character to each block inclusion and applying the GL
classification expresses it as a sum of integer multiples of the block
determinants. Restriction to a block's first coordinate cocharacter extracts
its coefficient: one on that block determinant and zero on the others.
These coefficient maps prove independence.

`blockDetCombination` is consequently a bijective linear map from integer
tuples to the rational-character group. Its associated linear equivalence
transports the usual basis of integer tuples to `blockDeterminantBasis`,
whose vectors are exactly the
block determinant characters. Every block has positive size, as required
by the published `BlockShape` definition.
