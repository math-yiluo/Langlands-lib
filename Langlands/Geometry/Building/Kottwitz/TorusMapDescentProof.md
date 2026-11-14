# Equivariance and rational descent of the torus Kottwitz map

`torusKottwitzDescent` proves the unchanged published proposition
`TorusKottwitzDescentStatement` for every nonarchimedean local field F and every
actual F-torus T. It proves equivariance of the constructed K-point map under
Gal(K/F), unique existence of its invariant-valued restriction to rational
points, and the restriction law of the already selected rational map. Here
K is `UnramifiedClosure F`, and the target is the actual residual invariant
submodule of the geometric cocharacter inertia quotient. No local-field
structure on K or its splitting extensions is assumed.

The original result is Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Proposition 11.1.1, printed pp. 421–422 / PDF pp. 452–453, with the
rational restriction convention on printed p. 420 / PDF p. 451. The positive
additive valuation convention is the one corrected in the November 2024
*Corrections and additions*, p. 24, Section 2.5 first bullet. The internal
helpers adapt the Library's actual coefficient points, valuations and Galois
representations to this equivariance argument.

The proof first chooses a finite Galois splitting field L/K inside the separable
closure that is normal over F, using `exists_normal_splitting` from
`TorusGaloisSplitting`. For a residual automorphism of K/F, lift it to the
separable closure and restrict to L. `TorusGaloisDescent` proves that the
relative point norm commutes with these automorphisms, and that the split
valuation followed by geometric cocharacter extension and inertia projection
intertwines them with the residual Galois action. The latter proof reduces to
pure cocharacter evaluations, uses invariance of the normalized integer
valuation under F-automorphisms, and extends by additive extensionality. Norm
surjectivity and the selected map's norm-square law, supplied by
`torusKottwitzExistence`, then give `TorusKottwitzEquivariant`.

Given equivariance, `torusKottwitzRestrictionOfEquivariant` takes a rational
point to the value of the K-point map after extension of coefficients and
records that the value is fixed. The proof uses
`GaloisPoint.conjugate_extend`: every residual automorphism fixes an extended
rational point. Its homomorphism laws follow from those of coefficient
extension and the K-point map. Its restriction specification is definitional.

Two homomorphisms satisfying the restriction specification agree after
inclusion in the inertia quotient. Extensionality proves their equality.
Thus `torusKottwitzRestriction_existsUnique_of_equivariant` gives unique
existence, and epsilon specification supplies the restriction law of
`torusKottwitzRational`. The final theorem combines these conclusions with the
unconditional equivariance proof; it has no supplied-equivariance hypothesis.
