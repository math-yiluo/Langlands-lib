# A fibre-dense affine open over a DVR

`Langlands.AlgebraicGeometry.SmoothDvrFibreDenseAffineOpenStatement.{u}`
asserts that a smooth, quasi-compact, separated scheme `X` over the spectrum of
an arbitrary discrete valuation ring `R` has an affine open `U` with the
following property: every point `x` of `X` has a generization `y` in `U`
with the same image in `Spec R`.

The conclusion is stated directly on points of the actual scheme and its
structure morphism. It expresses that `U` contains a dense open of every
irreducible component of each fibre. Smoothness supplies local finite type;
quasi-compactness gives finite type. There are no connectedness, nonempty-fibre,
generic-affineness, henselianity, excellence or residue-field assumptions.

This is an internal specialization of Bosch, Lütkebohmert and Raynaud,
*Néron Models* (Springer, 1990), §6.4, Lemma 4 and the paragraph immediately
following its proof, printed page 155 (PDF page 162). That lemma gives a common
affine neighbourhood of finitely many points of codimension at most one on a
normal separated scheme of finite type over an affine noetherian base.
For a smooth scheme over a DVR one takes the generic points of the total
scheme and of the special fibre. They are finite and have codimension at most
one. Including them gives the displayed same-fibre generization property;
a DVR has only its generic and closed points.

The source is registered as
`bosch-lutkebohmert-raynaud-1990-neron-models`, SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
The statement is a prerequisite for the principal-open argument of §6.5,
Lemma 6, printed page 161. This file defines the proposition and supplies no
proof.
