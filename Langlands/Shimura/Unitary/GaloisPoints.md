# Galois action on actual complex Harris points

This module is an internal derivation from the rational similitude functor,
its coefficient-change maps, and the established affine point
identification. Its generic helper `GroupScheme.AffinePointAutomorphisms`
constructs coefficient automorphism actions directly on scheme points.
No new source convention or chart identification is assumed.

## Coefficient automorphisms of similitudes

Let R,S be commutative rings with S an R-algebra, let A be an R-algebra
whose ring need not be commutative, and let σ be an R-linear algebra
involution on A. Write σ_S for its actual base change to S⊗_R A.
The group `σ_S.similitudes` consists of pairs of units `(g,c)` satisfying
`g σ_S(g) = algebraMap(c)`.

For an R-algebra automorphism s of S, `coefficientAut σ s` constructs a
multiplicative equivalence of this group by applying the already proved
functor `σ.similitudeFunctor` to `CommAlgCat.isoMk s`. Thus neither
preservation of the similitude equation nor existence of an inverse is
assumed as an additional input: both come from the actual coefficient
functor and functorial image of an isomorphism.

`coefficientAut_apply` identifies its map with `σ.baseChangeMap` for s.
The formulas `coefficientAut_underlying` and `coefficientAut_multiplier`
state, respectively,

\[
(g,c)\longmapsto ((s\otimes 1)(g),s^\times(c)).
\]

Here the tensor map is the existing `changeCoefficients s.toAlgHom`,
which sends `z⊗a` to `s(z)⊗a`; the multiplier uses `Units.map` of s.
These coordinate formulas follow by definition of the coefficient map.
In particular, the common similitude multiplier is retained and is
transformed by the same automorphism as the tensor coefficients.

`coefficientAut_one` and `coefficientAut_mul` obtain the identity and
composition laws by evaluating `similitudeFunctor.map_id` and
`similitudeFunctor.map_comp`. They use the convention
`(s*t)(z)=s(t(z))`. The definition `coefficientAutHom σ` packages the
construction as a group homomorphism into automorphisms of the actual
scalar-extended similitude group. These constructions require no finite
basis, field, nontriviality, or topological hypotheses.

## Agreement with actual scheme points

If b is a finite R-basis of A, the existing `SchemeModel.groupScheme b σ`
is the actual affine group scheme representing the similitude functor.
The theorem `SchemeModel.affinePointsEquiv_coefficientAut` proves that
its affine point identification intertwines the constructed automorphisms:

\[
\operatorname{affinePointsEquiv}(\operatorname{Spec}(s)\mathbin{\gg}x)
 =\operatorname{coefficientAut}(s)
    (\operatorname{affinePointsEquiv}(x)).
\]

The proof specializes the previously established
`affinePointsEquiv_naturality` to the algebra homomorphism underlying s.
The action on the left is precisely `GroupScheme.affinePointAut`, whose
evaluation is actual precomposition by the spectrum map.

## Harris specialization

Retain the totally real field E, totally complex quadratic extension K/E,
compatible E-, K- and rational-algebra structures on A and their scalar
towers, and central simple unitary datum D used in `RationalGroupScheme`.
The definition `D.complexPointGaloisAction` specializes
`GroupScheme.affinePointAutHom` to the actual rational Harris group scheme
and the rational algebra ℂ. It has source `ℂ ≃ₐ[ℚ] ℂ` and target the
automorphism group of actual complex points `Spec ℂ → D.rationalGroupScheme`
over Spec ℚ. No signature charts are needed for this action.

`complexPointGaloisAction_coordinates` specializes the preceding
intertwining formula using `D.rationalBasis` and the actual rational
involution. Thus Galois acts on scalar-extended algebra coordinates,
including the common multiplier, by the explicit coefficient map.

This module supplies the point action needed for later Galois transport.
It does not yet identify this action with a matrix-factor permutation,
construct transported scheme cocharacters, compare signature charts, or
identify a cocharacter-conjugacy stabilizer with the reflex stabilizer.
