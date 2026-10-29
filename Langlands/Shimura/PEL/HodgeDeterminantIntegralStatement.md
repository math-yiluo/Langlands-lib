# Integral coefficients of the actual Harris order Hodge determinant

`Langlands.Shimura.CentralSimpleUnitaryData.KottwitzIntegralHodgeDeterminantCoefficients`
is a proposition to be proved. It concerns the already constructed actual
regular Hodge determinant and the independently constructed finite full
integer order for the positive Harris left involution. It supplies no
proof or integral polynomial as assumed output data.

The arithmetic types `E`, `K`, `A` and the finite variable type `ι` have
`Type 0` scope. The hypotheses are the actual totally real number field
`E`, the totally complex quadratic number-field extension `K / E`, the
central-simple unitary datum `D`, its Harris signature charts `C`, and
the displayed rational, `E` and `K` algebra structures with all three
scalar towers. The proposition retains the CM-section hypothesis
`IsCMSection E K Φ` before quantifying over finite families.

For every finite index type `ι`, every family
`a : ι → D.harrisHodgePELIntegralOrder C`, and every monomial exponent
`d : ι →₀ ℕ`, the target says that

```text
(kottwitzHodgeDeterminant D C (fun i => (a i : A))).coeff d
```

is integral over `ℤ` as an element of `ℂ`. Here `IsIntegral ℤ z`
means that a monic integer polynomial vanishes at `z`. The target
includes constant and zero coefficients and the empty family. It
uses the existing determinant on the actual identity Hodge summand;
it does not replace that representation by its dimension or a
numerical-signature model. The order is the specific `Subalgebra ℤ A`
from `HarrisIntegralOrder`, with its proved module finiteness and full
rational span, not an arbitrary ring asserted to be an order.

This target is an internal integer-order specialization of Robert E.
Kottwitz, *Points on Some Shimura Varieties over Finite Fields* (1992),
section 5, printed pp.389–390 (PDF pp.17–18), registered as
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
The original uses a basis of a prime-local order and states that its
Hodge determinant has coefficients in the corresponding prime-local
ring of integers of the reflex field. It explains integrality after
passing to a finite field of definition and a basis in which the order
acts integrally. Both original pages have been read for this target.

The present domain is smaller: families lie in the constructed global
integer order. Accordingly the target asks for algebraic integrality
over `ℤ`, with no inverted prime. It also allows arbitrary finite
families rather than requiring an order basis. Establishing the target
requires a proof for this actual finite order and Hodge action; the
source discussion and the proposition do not provide such a proof.
A future proof may establish a reusable finite-order representation
lemma and then specialize it, but it must prove the displayed target
without an assumed integral lattice on the Hodge summand.

Together with the separately proved reflex-field membership theorem,
this result will allow the actual descended coefficients to be viewed
in the ring of integers of that field. This file does not construct
that lift, a prime-local maximal order, a self-dual lattice, a Lie-section
determinant condition or a PEL moduli scheme. Those remain distinct
construction obligations. Worker 57 authored this statement and its
integer-order specialization rationale.
