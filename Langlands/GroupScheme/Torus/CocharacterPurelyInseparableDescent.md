# Descent through arbitrary purely inseparable extensions

This module constructs the coefficient-extension group equivalence on
multiplicative points through an arbitrary purely inseparable field
extension. It is an internal deduction from
`Torus.CocharacterFiniteTypeDescent`, the coordinate descent API in
`Torus.CocharacterDetection`, and Mathlib's finite intermediate-field
theorems. It introduces no external structural assumption.

Let `k` be a field, `Z` an affine commutative `k`-group scheme whose structure
morphism is locally of finite type, and `Λ` an additive commutative group.
All types in this module lie in the same arbitrary universe. Suppose
`F → L` is an extension of fields over `k`, with the indicated scalar tower.
A multiplicative point is an element of
`Z(L[Λ])` satisfying the actual multiplication and identity conditions of
`CocharacterDatum.IsMult`. The group algebra here is `AddMonoidAlgebra L Λ`.

`coeffMap_comp` proves that successive coefficient extensions agree with
extension along the composite. It has no affineness or finite-type premise.
The proof compares the group-algebra homomorphisms coefficient by coefficient,
then uses functoriality of affine points.

`IsMult.exists_finiteDimensional_coeffMap_eq` assumes that `L/F` is algebraic.
It produces a finite-dimensional intermediate field `E` and a multiplicative
point `y` over `E` whose image under the inclusion `E → L` equals the original
point `x`. This step does not require torsion-freeness of `Λ`. Affineness and
local finite type make the coordinate algebra finitely generated. The proof
collects the finitely many nonzero coefficients in the images of a chosen
finite set of algebra generators and adjoins them to `F`. Algebraicity makes
that intermediate field finite-dimensional. Each generator image belongs to
the range of the group-algebra coefficient map, and induction through the
generated algebra extends this to all coordinate functions. The injective
coordinate descent construction gives `y` and its exact recovery equality.
Multiplicativity reflects through the injective coefficient map.

`IsMult.exists_coeffMap_eq_of_isPurelyInseparable` additionally assumes
`IsAddTorsionFree Λ` and that `L/F` is purely inseparable. The preceding
finite coefficient reduction gives a finite purely inseparable intermediate
extension `E/F`. Mathlib's exponent theorem supplies a uniform exponent for
this finite extension. The bounded descent theorem over `E/F` supplies a
multiplicative point over `F`. Composition of coefficient maps recovers
exactly the original point over `L`. No bound on the exponent of `L/F` is
assumed.

`multiplicativePointsEquivOfIsPurelyInseparable` is the resulting actual
group equivalence

```text
multiplicativePoints Z F Λ ≃* multiplicativePoints Z L Λ.
```

Its forward map is `multiplicativeCoeffMap` for the original field inclusion
`F → L`. Injectivity follows from injectivity of that coefficient map on
affine points, and surjectivity is the exact descent theorem above.

Finally, `IsDatum.exists_coeffMap_eq_of_isPurelyInseparable` retains any
specified character `χ` and weight `m : Λ`. It descends the multiplicative
point and reflects the character condition through the same injective
coefficient map. It returns both `IsDatum χ m y` and the equality recovering
the original point.

The conclusions concern group-algebra-valued points of the original `Z`;
they do not yet identify morphisms from a base-changed multiplicative group.
This module does not prove unipotence, maximal-torus base change, or the
parent `NoTorusUnipotentStatement`. Smoothness and connectedness of `Z` are
not required.
