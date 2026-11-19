# Cartan reduction for the original source-normalized packet

This module specializes `OrbitSectionCartanReduction` to the actual
standard-Levi Plancherel packet. `StandardLeviPacketChamberDerivativeEstimates`
uses the original full matrix height and rational Xi, and imposes its
finite-level bounds on the image of `rationalMinimalClosedChamber` in
the ambient group. It retains the original source-normalized character and
orbit measures, the original inducing representation and quotient Haar,
and the separate compact subgroups for the scalar and the compact picture.
Field and representation-carrier universes are independent.

`exists_compact_cover_rationalMinimalClosedChamber` turns the given
finite Cartan covering into a double cover by that chamber. The positive
torus factor in each Cartan expression comes from a cocharacter whose
simple-root pairings are nonnegative. Its actual minimal-Levi uniformizer
point belongs to the chamber since its `H₀` is the scalar extension of
the same cocharacter. The left compact factor is the product of the
displayed compact subgroup `K0` with the image of the finite centralizer
representatives. The right compact factor is `K0`.

`standardLeviPlancherelWavePacket_translateLevel` is the original orbit
integral covariance for this packet. The proof keeps the packet weight
and measure while translating the original compact picture section.

`standardLeviPacketDerivativeEstimates_of_chamber` obtains the common
open subgroup for weight invariance by intersecting the input compact
picture `K` with the preimage of the matrix integral subgroup associated
to `ρ`. It uses the original Xi translation bound and the exact height
inequalities. The known same-level packet bi-invariance and the
translated integral identity then give the full
`StandardLeviPacketDerivativeEstimates`, the input to the existing
Schwartz synthesis theorem.

The proof has two inputs specific to this reduction, the compact Cartan
covering and the chamber derivative estimates. The latter include the
open obligation on the unbounded proper-parabolic regions. This is a
derived intermediate step in the proof of Waldspurger VI.3.1, whose
Cartan and finite translation reduction appears on printed pp. 302–303.
[Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)
