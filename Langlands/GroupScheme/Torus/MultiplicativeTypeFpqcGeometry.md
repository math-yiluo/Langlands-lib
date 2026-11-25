# Geometric fibre conditions and torsion orders under fpqc base change

This is an internal derivation from the published geometric-fibre
comparison, the field-level multiplicative-type predicate, actual torsion
schemes, affine tensor coordinates and the quotient topology of fpqc maps.

The geometric-fibre comparison identifies the fibre upstairs with the base
change of the downstairs fibre along a compatible embedding of the chosen
algebraic closures of residue fields. Preservation and reflection under that
field extension prove `geometricFiber_isMultiplicativeType_iff`. Surjectivity
of the base morphism then yields the equivalence quantified over all points.

`torsionIso` restricts an isomorphism of commutative group schemes to their actual
integer-torsion schemes using `torsionMap` and its composition and identity laws.
`geometricTorsionOrder` is the coordinate dimension of integer torsion in the
chosen geometric fibre, with scalars induced by its actual structure morphism.
It uses `Module.finrank`, whose value is zero for infinite-dimensional modules.
It makes no assertion that the torsion scheme is finite.

For affine commutative groups, `geometricTorsionOrder_baseChange` identifies the
actual torsion schemes using their base-change isomorphism and `torsionIso`,
then applies the affine coordinate-dimension scalar-extension theorem.
The integer can be arbitrary, including zero; the result has no flatness or
finite-presentation premise on the group.

Flat, surjective, quasi-compact scheme morphisms induce quotient maps on their
underlying spaces. Openness of each fibre of a function therefore descends along
such a map. This proves `isLocallyConstant_comp_iff`; the torsion-order comparison
gives `isLocallyConstant_geometricTorsionOrder_iff`.

The module supplies transfer lemmas for the fpqc part of Conrad's Corollary
B.4.2. It does not prove the fibral criterion or the full fpqc-and-extension
statement.
