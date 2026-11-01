# Pure Laurent extensions and radical value-group radii

Author: Worker 84.

This internal construction selects a finite tower of the actual completed
Gauss Laurent fields from `LaurentGaussField`. The base is any complete
ultrametric normed field `K : Type u`, including a trivially valued field.
Every field in the construction stays in `Type u`.

`RadiusInRadicalValueGroup K r` means that there are an element `a : K` and
a positive natural number `n` with `‖a‖ = r ^ n`. For a positive radius `r`,
the element is necessarily nonzero. This is the positive-real radius condition
usually written `r ∈ √|K*|`.

`IsPureLaurentTower K L ι` records a finite sequence of actual scalar maps.
Its initial case is the identity of `K`. Each step is the scalar inclusion
into `CompletedGaussLaurent L r`, composed with the preceding map, at a
positive radius `r` satisfying
`∀ (a : L) (n : ℤ), n ≠ 0 → ‖a‖ ≠ r ^ n`.
The field structure at that step is the previously constructed
`CompletedGaussLaurent.normedField` for this independence condition.
There are no algebraic root extensions among these steps.

`PureLaurentExtension K` stores a complete ultrametric extension `L`, its
isometric scalar map, and this tower witness. `self` gives the identity
extension, and `adjoin` appends one independent-radius step.

The implemented proof of `exists_for_radii` proceeds by induction on the
length of a finite positive radius tuple. It first treats the tail. If a
positive integral power of the remaining radius already occurs as a field
norm, the existing tower suffices. Otherwise the radius satisfies the
independence condition: a negative integral exponent can be replaced by
its positive absolute value by inverting the field element. The construction
then adjoins that radius through the actual completed Laurent field. Its
variable has the prescribed norm, and the scalar inclusion preserves all
previous positive-power witnesses.

`exists_nontrivial_for_radii` first includes radius two in the tuple.
The resulting positive-power witness has norm `2 ^ n > 1`, so the final
field is nontrivially valued, while all originally requested radii remain
in its radical value group. No nontrivial-valuation assumption is imposed on
the original field.

This module does not construct affinoid presentations of these extension
fields, scalar extensions of affinoid algebras, strict presentations for
radical-value-group radii, or Gauss sections on spectra. In particular it
does not prove the finite rational cover theorem.

The construction is internal. Its radius condition is the one appearing in
Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
Fact 2.1.3(ii), printed/PDF page 7. The actual Laurent field construction is
reused from `LaurentGaussField`, rather than asserted as a hypothesis.
The registered original is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
