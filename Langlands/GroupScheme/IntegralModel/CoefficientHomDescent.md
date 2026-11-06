# Descent of actual compatible model morphisms over a coefficient square

This module constructs homomorphism and isomorphism descent between supplied
integral models while preserving their prescribed generic maps. It works in
every common universe `u`.

Let `R` and `A` be commutative domains with fraction fields `K` and `L`.
The specified algebra maps form a commuting square: `R → A → L` and
`R → K → L`, expressed by the two scalar-tower instances. Let `M` and `N`
be supplied integral models of actual `K`-group schemes `G` and `H`.
Their coefficient base changes are the existing `M.baseChange A L` and
`N.baseChange A L`, including the generic identifications transported from
the original models.

## Reflection of generic compatibility

`generic_comm_of_coefficientExtension` starts with an actual integral model
map `g : M.group ⟶ N.group`. Assume its coefficient pullback equals the
underlying map of an upstairs `IntegralModel.Hom` extending the pullback
of a prescribed map `f : G ⟶ H`. Then `g` itself extends `f` through the
original generic identifications.

The proof conjugates the generic restriction of `g` by `M.genericIso` and
`N.genericIso`, obtaining a map `f₀ : G ⟶ H` that `g` extends by construction.
The naturality of `Hom.baseChangeCoefficients` and the supplied upstairs
compatibility square show that the `L`-pullbacks of `f₀` and `f` agree.
The field extension `K → L` is fpqc, so faithful group-scheme pullback
reflects their equality. This proves the required original compatibility
square. This first result requires no flatness or surjectivity of `Spec A → Spec R`.

## Homomorphism descent

The remaining results assume that `Spec A → Spec R` is flat and surjective.
It is quasi-compact because both schemes are affine.
`Hom.descendCoefficients` takes an actual upstairs model homomorphism
extending the pullback of `f`, together with compatibility of its underlying
map with the canonical Čech data of `M.group` and `N.group`.

`FpqcHomDescent.hom` constructs its actual underlying descent over `R`.
Its recovery equation supplies the hypothesis of the generic-compatibility
reflection result, so this descent is an `M.Hom N f` for the original
models and original generic identifications.
`Hom.baseChange_descendCoefficients` recovers the supplied upstairs
underlying map exactly.
`Hom.descendCoefficients_unique` proves uniqueness among original
compatible model homomorphisms whose coefficient pullbacks equal that map.
It applies fpqc homomorphism uniqueness and the fact that the remaining
field of `IntegralModel.Hom` is propositional.

## Isomorphism descent

`Iso.descendCoefficients` starts with an upstairs compatible integral-model
isomorphism extending the pullback of a specified isomorphism `f : G ≅ H`.
Only its forward map's canonical Čech compatibility is supplied.
The existing `Solution.descendIso`, applied to the two canonical solutions,
constructs the actual isomorphism between `M.group` and `N.group`.
It descends the inverse using `Compatible.inv` and proves both inverse
laws by faithful pullback. Generic-compatibility reflection again proves
the square for the prescribed original `f`.
`Iso.baseChange_descendCoefficients` proves equality of the actual
coefficient pullback isomorphism with the supplied upstairs isomorphism.

## Provenance and remaining construction

This is an internal derivation from the published coefficient base change
of integral models, fpqc homomorphism descent, descent between actual
solutions, and faithful field-extension pullback. It invokes no new
literature theorem.

Canonical Čech compatibility remains an explicit input. The module
constructs neither an upstairs extending map nor a canonical comparison
for a supplied good model. It does not construct a building, a special
point, its metric, or the full `BuildingComparisonStatement`.
