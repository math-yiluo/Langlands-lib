# Integer-valued forms on preserved rational lattices

## Provenance and scope

This module is a derived algebraic prerequisite for Kottwitz, *Points on some
Shimura varieties over finite fields* (1992), section 5, printed page 389
(PDF page 17), registered as `kottwitz-1992-points-shimura-finite-fields`,
SHA-256 `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
The source starts with a nondegenerate rational alternating form on a left
module, compatible with the algebra involution, and a preserved self-dual
lattice after completion at the chosen prime. The present construction supplies
an integral-valued restriction on a global integer lattice. It is a preliminary
construction, not a transcription of the stronger local self-duality hypothesis.

The rational form is unchanged. The lattice is scaled by a chosen nonzero
integer. No claim of perfectness, self-duality, maximality of an order or a local
completion is made. The construction uses choices of finite generators and a
common denominator and is not asserted to be canonical.

## Denominator clearing and the scaled lattice

Let `V` be any rational vector space, `B : LinearMap.BilinForm ℚ V`, and
`L : Submodule ℤ V`. Finite dimensionality of `V` is not a separate hypothesis.
For finite generation `L.FG`, `exists_pairing_denominator` proves that there is a
nonzero integer `m` such that `m • B x y` is an integer whenever `x,y ∈ L`.
Here `IsLocalization.IsInteger ℤ q` means that `q` is the image of an integer
under the integer-to-rational algebra map.

The proof takes a finite generating set of `L`, clears the rational values on
all ordered pairs of generators with
`IsLocalization.exist_integer_multiples`, and extends integrality by integer
span induction in both arguments. The private helper
`isInteger_bilinear_of_span` implements this last step using additivity and
integer scalar multiplication.

Assume now `Submodule.IsLattice ℚ L`, meaning finite generation over the
integers and full rational span. `pairingDenominator B L` chooses an integer
from the preceding existence proof; `pairingDenominator_ne_zero` and
`pairingDenominator_isInteger` record its properties.
`pairingDenominatorUnit B L` views it as a rational unit.
`integralPairingLattice B L` is the pointwise scalar multiple `mL` using this
unit. `integralPairingLattice_isLattice` uses Mathlib's unit-scaling theorem to
prove finite generation and full rational span for the new lattice.

`mem_integralPairingLattice` identifies its elements as exactly `m • x` with
`x ∈ L`. On two such elements, bilinearity gives
`B (m • x) (m • y) = m • (m • B x y)`. The inner value is integral by the
choice of `m`, and its integer multiple is integral. This proves
`integralPairingLattice_isInteger` for the original rational form on the new
lattice.

## The integer bilinear form

For any integer submodule `L` on which `B` has integer values, with that
integrality proof `h`, `integerPairing B L h` is an actual
`LinearMap.BilinForm ℤ L`. It is constructed by
`LinearMap.restrictScalarsRange₂` using the inclusion of `L` into `V` in
both variables and the injective linear map from the integers to the rationals
in the values. Bilinearity is inherited from this construction, rather than
included as an additional input.

`integerPairing_cast` identifies its rational value with `B` evaluated on the
included lattice elements. `integerPairing_isAlt` deduces alternation from
`B.IsAlt`, using injectivity of integer cast.
`integerPairing_nondegenerate` assumes full rational span of `L` and both
separating properties of `B`. If a lattice vector is orthogonal to every
lattice vector for the integer form, its rational linear functional vanishes
on `L`. `LinearMap.ext_on` and full rational span show that it vanishes on
all of `V`. Rational nondegeneracy then gives that the vector is zero. The
proof performs this argument in both variables, using the flipped rational
form for the second. Nondegeneracy here means zero left and right kernels;
it does not assert that the lattice maps surjectively onto its integer dual.

## Preservation and faithful action

For this part `A` is a possibly noncommutative rational algebra, the vector
space is its left regular module, and `L` is a finite full integer lattice.
The existing `latticeStabilizer L` is the integer subalgebra of elements that
preserve `L` by left multiplication.

`latticeStabilizer_le_integralPairingLatticeStabilizer` proves that every
such multiplier also preserves `integralPairingLattice B L`: multiplication
commutes with the integer scalar `m`. `integralPairingLatticeAction B L`
composes this inclusion with the existing left multiplication action on the
new lattice. It is a ring homomorphism to its integer-linear endomorphism
ring; `integralPairingLatticeAction_apply` identifies it with multiplication
in `A`.

`integralPairingLatticeAction_injective` proves faithfulness. Equality of
actions gives equality of the rational left multiplication maps on the new
lattice, hence on all of `A` by full rational span. Evaluation at `1` gives
equality of the multipliers. This argument does not require `1` itself to
belong to the scaled lattice.
