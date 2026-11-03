# Structural target for the actual adjoint determinant

`DynamicAdjointDeterminantStructureStatement` is an unproved proposition target.
Its inputs are an arbitrary field, an actual connected reductive group scheme,
a cocharacter, and inclusions representing precisely its dynamic parabolic
`P`, centralizer `M`, and unipotent subgroup `U` on every scheme test.

The conclusion supplies affineness of all three structure morphisms, closedness
of the three inclusions, smoothness and local finite type of all three groups,
finite dimension of the actual dual-number Lie kernel of `U` over the field,
and a rank `d` with natural finite coordinates on that kernel over every test
algebra. `Lie.FiniteCoordinates` supplies only linear coordinates and their
naturality under all algebra maps. It supplies no action, representation, or
character. The affine witness required to express these coordinates is bound
inside the conclusion; it is not an input.

This is derived arbitrary-field packaging. Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), §2.1, printed pp.52–54
(PDF pp.78–80), gives the tangent-kernel interpretation and base change on p.52
and the smooth dynamic subgroup assertions in Proposition 2.1.8(3), p.53.
Choosing a basis of the finite-dimensional tangent space over a field and
using its natural base change yields the stated coordinate-existence target.
The Library's `Lie.FiniteDimensional` already proves finite dimension for an
affine locally finite type group; it does not supply those natural coordinates.
The existing dynamic smoothness and structural proof owners are retained;
this target assembles their consequences and adds the coordinate conclusion.

The motivating local-field setting is Renard, 9 July 2026 version,
§V.3.1–V.3.4, printed p.110 (PDF p.116), and §V.5.4, printed pp.126–127
(PDF pp.132–133); and Waldspurger (2003), §I.1, journal pp.238–239
(PDF pp.4–5). These passages discuss actual parabolic and Levi subgroups,
Lie roots, algebraic characters, and the analytic modulus. They are not
asserted to state the arbitrary-field coordinate theorem.

Registered sources: `conrad-gabber-prasad-2015-pseudo-reductive`,
`renard-2026-representations-groupes-reductifs-padiques`, and
`waldspurger-2003-plancherel`. No restriction on characteristic, splitness,
root reduction, or positive rank occurs in the target.
