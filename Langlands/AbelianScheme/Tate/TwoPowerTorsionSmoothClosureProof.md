# Smoothness of the actual two-power torsion closure

The theorem `Langlands.AbelianScheme.Tate.twoPowerTorsionSmoothClosure_exists.{u}`
proves exactly `TwoPowerTorsionSmoothClosureStatement.{u}`. For every
algebraically closed field `K : Type u` and every actual bundled abelian
scheme `A` over `Spec K`, it supplies a smooth closed scheme realization of
`closure (twoPowerTorsionLocus A)`, a factored unit, and compatible scheme
automorphisms restricting inversion and all rational translations whose
image lies in the closure. There is no characteristic assumption.

The proof uses the published reduced-closure existence theorem
`twoPowerTorsionReducedClosure_exists` for the scheme, immersion, reducedness,
range equality, factored unit and restricted automorphisms. It adds
smoothness as follows. Closed immersion into the finite-type abelian scheme
makes the structure morphism locally of finite type. Each closed point of
the closure is represented by a rational section over the algebraically
closed field. Its ambient image lies in the actual closure. The compatible
restricted translation by this section carries the lifted unit to the
original section, by cancellation of the closed immersion and the ambient
unit law. Given two closed points, composing the inverse of the first
translation with the second therefore carries the first to the second.
The restriction equations also show that these automorphisms preserve
the structure morphism to the field.

The generic theorem `Langlands.AlgebraicGeometry.closedPointHomogeneousSmooth`
now applies: the scheme is reduced and locally of finite type over the
algebraically closed field, and actual base-preserving automorphisms act
transitively on its closed points. Its smoothness conclusion is inserted
in the original existence data, preserving all unit, inversion and
translation restrictions.

This is an internal derivation from the named published geometric results
and the existing actual section group operations. It constructs no
multiplication or group-object structure on the closure and proves no
numerical torsion count, dimension comparison or torsion density.
