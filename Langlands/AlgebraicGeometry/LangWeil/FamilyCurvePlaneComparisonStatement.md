# Uniform comparison of curve fibres with bounded-degree plane curves

Author: Worker 158.

## Meaning

`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement`
is a geometric prerequisite for `FamilyLangWeilCurveStatement`. It assumes
`FamilyPointUpperBoundStatement`, then quantifies over exactly the scheme
families in `FamilyLangWeilInDimension 1`: the base is quasi-compact and locally
of finite type over the integers; the morphism is quasi-compact, locally of
finite type and geometrically irreducible; every residue-field fibre has pure
dimension one.

For each such family it asserts one positive integer `B`. For every finite field
`κ` in the same universe and every `κ`-point `s` of the base with `B < #κ`, there
is a polynomial `p ∈ κ[X,Y]` that remains irreducible over the algebraic closure,
has positive degree at most `B` in each variable, and whose affine zero count
differs from the number of actual scheme points over `s` by at most `B`.
The integer is independent of the finite field and the base point. The
polynomial may depend on both. No global plane family, comparison map or
birationality assertion is included in the Lean conclusion.

The statement contains no Hasse–Weil estimate or square-root error bound.
The uniform upper bound is retained to control the zero-dimensional exceptional
loci in a prospective geometric proof. Geometric irreducibility is not
strengthened to geometric integrality or smoothness.

## Provenance and intended geometric proof

Provenance: derived. The plane-model route is described in Terence Tao,
*The Lang–Weil bound* (31 August 2012; registered source
`tao-2012-lang-weil-bound`), Section 2, first paragraph: reduce the curve
case by a birational plane model, with a bounded change in point counts.
Lang and Weil, *Number of points of varieties in finite fields* (1954;
registered source `lang-weil-1954-number-of-points`), printed p.819
(PDF p.2), compare a curve with a nonsingular projective model and bound
the change in point count in terms of its degree. Neither passage states
this exact assertion about all finite-type scheme families.

The family formulation is an internal intermediate result for Task 5408.
Its intended proof uses Noetherian induction on the base, an affine dense
open of each generic fibre, and a plane model of its function field.
Nonreduced fibres must be treated without adding a reducedness hypothesis;
finite purely inseparable alterations and reduction do not change points
over finite fields. One must spread out the comparison, its finite exceptional
loci, and absolute irreducibility over a dense open of each base stratum,
then use the assumed upper bound in dimension zero on the exceptional loci.
Taking the maximum of the finitely many bounds gives `B`, enlarged to include
any required field-size threshold and to be positive. The affine-line case
can use the equation `X - Y`, whose two degrees are positive.

This module states the prerequisite. It supplies no proof of it and no proof
of `FamilyLangWeilCurveStatement`.
