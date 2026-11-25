# Finite flat torsion of relative multiplicative-type groups

This internal construction identifies the actual relative diagonalizable
`n`-torsion with the relative diagonalizable model for the unsaturated quotient
`M/nM`. It then proves that every positive torsion level of a commutative group
of relative multiplicative type is finite, flat and locally of finite
presentation over its base scheme, including in characteristics dividing `n`.

`torsionMapIso` transports torsion through a group-scheme isomorphism using the
published torsion functor on homomorphisms. `diagonalizableTorsionIso` combines
the actual affine torsion model with arbitrary base change from `Spec ℤ`.
The group algebra is free over its coefficient ring, hence flat, and is
finitely presented when the character group is finitely generated.

For a diagonalizable group, `M/nM` is finite when `M` is finitely generated and
`n > 0`, so its model is finite, flat and locally of finite presentation.
Isomorphism transport proves `IsDiagonalizable.torsion_geometry`.
The published fppf-locality theorem for morphism properties, together with
arbitrary base change of the actual torsion scheme, descends the three
properties from a diagonalizing cover and proves
`IsMultiplicativeType.torsion_geometry`.

`geometricTorsionFinrank_eq` identifies the coordinate-algebra dimension of each
geometric torsion fibre with the native rank of the actual torsion scheme at
the underlying point, assuming the torsion scheme is finite and flat. It uses
the actual torsion base-change isomorphism, invariance of native rank under
isomorphism and base change, and
`FiniteEtale.homFinrank_eq_coordinateFinrank`, whose finite-flat hypothesis
does not require étaleness.

`IsMultiplicativeType.isLocallyConstant_torsionFinrank` combines this equality
with the proved finite-flat-presentation result and Mathlib's local constancy
of the native rank of a finite flat locally finitely presented morphism.
Its function is exactly the geometric coordinate dimension appearing in
`MultiplicativeTypeFibralCriterionStatement`, for every natural `n > 0`.
Together these results supply the torsion-order necessity in that criterion;
no fibral converse is asserted.

The base is arbitrary; no reducedness, Noetherian, connectedness or
characteristic assumption is imposed. The input group has a supplied
commutativity instance, as required by the Library's torsion construction.
The derivation uses the published torsion functor and base-change comparison,
the diagonalizable group algebra and its finite-presentation theorem, and fppf
descent of morphism properties, together with the actual torsion-model
construction in `DiagonalizableTorsion`. No external theorem is restated.

Relative diagonalizable flatness, finite presentation and finiteness are reused from `RelativeMultiplicativeTypeGeometry` and `RelativeMultiplicativeTypeFinite`.
