# Normalized coordinates for actual projective-space points

For every field `K : Type u`, natural number `n`, and actual scheme morphism
`p : Spec K → ProjectiveSpace K n` satisfying
`p ≫ projectiveSpaceToSpec K n = 𝟙 (Spec K)`, `pointCoordinates` constructs
a vector in `Fin (n + 1) → K`. Its coordinate at `pointChartIndex` is one,
so the vector is nonzero. The chosen chart and vector use classical choice;
no independence of the choice, naturality, or projectivization equivalence
is asserted here. The field need not be algebraically closed.

The algebraic starting point, `degreeOneDehomogenize`, is defined over every
commutative ring `R`. It divides an element of the actual homogeneous
degree-one submodule by a selected chart variable inside Mathlib's
homogeneous localization. Injectivity into ordinary localization and its
fraction identities prove additivity and compatibility with the `R`-algebra
scalar action. The variable basis from `LinearForms` maps to the actual
chart ratios. The finite basis expansion gives the coefficient formula
`degreeOneDehomogenize_linearForm`.

For any `K`-algebra map from that chart algebra to `K`, `chartCoordinates`
evaluates the ratio elements. The ratio of the selected variable to itself
is one. Applying the algebra map to the dehomogenization of
`linearFormPolynomialEquiv K n ℓ` gives exactly
`ℓ (chartCoordinates n j φ)`, by the coefficient formula and the standard
basis expansion in `K^(n+1)`.

`chartPoint` is the actual morphism obtained by composing `Spec.map` of the
chart algebra map with `Proj.awayι`. Compatibility with the algebra map on
constants proves its structure-map equality. Mathlib's
`Proj.awayι_preimage_basicOpen` identifies the inverse image of the basic
open of a homogeneous linear polynomial with the affine basic open of its
dehomogenization. Pulling back by `Spec.map` therefore gives the basic open
of its evaluated value. At the unique closed point of `Spec K`, membership
in the complementary homogeneous prime is equivalent to this value being
zero, because the maximal ideal of a field is zero. This proves
`chartPoint_linearForm_mem_iff`.

`exists_chartPoint` recovers such a chart algebra map from every `p` in the
stated scope. The coordinate opens cover the actual polynomial Proj, so
some chart contains the image of the closed point. An open in the spectrum
of a local ring containing its closed point is the whole spectrum; hence
the entire image of `p` lies in that chart. The universal property of the
open immersion lifts `p` to the affine chart. Full faithfulness of `Spec`
recovers a ring map from this lift. The equality over `Spec K`, together
with the chart structure-map formula and injectivity of `Spec.map`, proves
that it commutes with the coefficient maps and thus is a `K`-algebra map.
Its associated `chartPoint` equals `p` as a scheme morphism.

`pointChartIndex` and `pointChartMap` choose this factorization, and
`pointCoordinates` evaluates its ratios. Transporting the chart incidence
formula along the equality of actual morphisms proves
`pointCoordinates_linearForm_mem_iff`: the polynomial corresponding to `ℓ`
belongs to the homogeneous prime at `p (IsLocalRing.closedPoint K)` if and
only if `ℓ (pointCoordinates n p hp) = 0`. The inverse of the
`LinearForms` equivalence gives `pointCoordinates_mem_iff` for every element
`f` of the actual degree-one submodule: prime membership is equivalent to
`MvPolynomial.eval (pointCoordinates n p hp) f = 0`.

This construction has internal provenance. It combines the existing
polynomial-Proj projective space, its coordinate cover and chart algebra,
the degree-one basis and functional equivalence, and the Mathlib
localization, open-immersion and `Spec` APIs described above. It supplies
coordinates and degree-one incidence only. It does not prove the torsion
hyperplane bound, compare projective linear actions, or establish
`LargeLevelRepresentabilityStatement`.
