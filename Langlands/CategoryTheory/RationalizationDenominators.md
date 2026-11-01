# Integral representatives of rationalized morphisms

This internal supporting construction uses the existing rationalization of a
preadditive category. It derives its results from Mathlib's localization of
modules and the existing tensor definition of rationalized morphisms. It is not
an assertion of geometric representability.

For any category `C` with preadditive Hom groups, the existing map `ofHom` is the
localization of each integral Hom group at the nonzero integers. The instance
`ofHom_isLocalizedModule` is the tensor localization instance specialized to
`ℤ`, `ℚ` and that Hom group. The rational field is the fraction field of `ℤ`.

`exists_integral_multiple` says that every rational morphism `f` admits a
nonzero integer `n` and an actual integral morphism `g` such that
`ofHom g = n • f`. `exists_common_integral_multiple` supplies one such integer
and a family of actual integral maps for any finite indexed family in one Hom
group. These results use the localized module's integer-multiple theorems.

`ofHom_eq_iff_exists_zsmul_eq` says that two integral maps have equal rational
images exactly when a common nonzero integer multiple makes them equal. It uses
the equality criterion for a localized module. It does not assume the integral
Hom group is torsion free and does not claim that `ofHom` is injective.

For a rational isomorphism `e : of X ≅ of Y`, `IntegralIsoData e` contains nonzero
integers `a` and `b` and actual maps `f : X ⟶ Y` and `g : Y ⟶ X`, satisfying all
four equations

- `ofHom f = a • e.hom`;
- `ofHom g = b • e.inv`;
- `f ≫ g = (a * b) • 𝟙 X`;
- `g ≫ f = (a * b) • 𝟙 Y`.

`nonempty_integralIsoData` proves such data exists and `integralIsoData` chooses
it. The proof first clears the two rational denominators separately. Their
composites agree rationally with the same integer multiples of the two
identities. The equality criterion gives two additional nonzero integers
annihilating the integral discrepancies. Multiplying the first map and its
denominator by their product gives both exact integral composite equations.
No cancellation in an integral Hom group is used.

This is an algebraic construction for use in comparing integral and rational
moduli descriptions. It neither constructs an integral algebra action nor
proves that any map is a finite flat isogeny, a quotient, or part of a moduli
scheme. Those require separate geometric arguments. The chosen data is not
claimed to commute with other choices under functors.
