# Finite free polynomial models of separable fraction-field extensions

This internal construction refines `FiniteSeparableIntegralModel` using the
monic-polynomial step in the proof of Stacks Lemma 37.24.8 (0551), in the
registered source `stacks-generic-geometric-irreducibility-2026-11-04`,
file `0551.html`. The base is an arbitrary domain R, with a specified fraction
field K and a specified finite separable extension L/K, in independent universes.
No Noetherian or integral closedness condition is imposed on R.

Clear the finitely many coefficient denominators of the generic minimal
polynomial by scaling its roots. Its monicity allows the resulting polynomial
to lift to a monic polynomial over R. Scaling a primitive element by the same
nonzero element preserves primitivity. The minimal-polynomial scaling identity
over the field K identifies the lifted polynomial's generic image with the
minimal polynomial of the new element.

The actual subalgebra R[b] of L is presented by this polynomial: evaluate at b,
use the range description of a singly generated algebra for surjectivity,
and identify its kernel after the injective map R to K. Monic division reflects
divisibility back to R, so no integral-closedness assumption is needed.
The presentation supplies a power basis, module freeness and algebraic finite
presentation over R, in addition to the earlier finiteness, localization and
generic tensor comparison.

This construction does not establish finite etale spreading, splitting of geometric
components, or the nonreduced irreducible-base case of the source.

`nonempty_finiteSeparablePolynomialModel` proves existence and
`finiteSeparablePolynomialModel` chooses the resulting data. The structure
extends the integral-model structure, so its `Carrier` is the same actual
subalgebra and its inherited localization and generic tensor comparison are
available through `toFiniteSeparableIntegralModel`. The new `presentation`
constructs an `IsAdjoinRootMonic` witness for that carrier and the polynomial;
`powerBasis`, `free` and `finitePresentation` are obtained from this witness.
The minimal polynomial scaling theorem is applied over K, which is a field,
and therefore does not require R to be integrally closed.
