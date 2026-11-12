# Central exponents and positivity of shifted derivatives

Author: Worker 105.

These definitions supply the central-exponent and shifted-derivative predicates
needed for Bernstein's proof of irreducibility of unitary products. They do not
prove positivity, irreducibility, or unitarity.

The original source is J. N. Bernstein, *P-invariant distributions on GL(N) and
the classification of unitary representations of GL(N)*, LNM 1041 (1984),
§§7.2–7.3, printed page 82 (PDF page 33), and §8.2, printed page 88 (PDF page
39), registered as `bernstein-1984-p-invariant`.

`HasBernsteinCentralExponent T A e` requires a character `ω : Fˣ →* ℂˣ` whose
actual scalar matrices act by `ω`, with `‖ω(a)‖ = |a|^e` for every `a ∈ Fˣ`.
The absolute value is the supplied topology's residue-normalized absolute value.
Thus `e` is the exponent on scalar matrices, with no division by the rank.
This is precisely the source's convention for an irreducible representation of
positive rank. The relation is also defined for representations that are not
irreducible; no assertion that they have scalar action is made.

`bernsteinCentralExponents T A` consists of the exponents of irreducible actual
smooth subquotients of `A`. Subquotients use the Library relation formed from an
invariant subspace and its quotient, up to actual smooth isomorphism. Carriers
are in the same arbitrary universe as `A`. The definition does not choose a
central character or assert its existence or uniqueness. The source's exponent
set is expressed directly by these existential witnesses.

Bernstein defines central exponents initially for positive rank. We extend the
same scalar formula to rank zero to permit derivatives reaching `GL_0`. Scalar
matrices there are the identity, so on a nonzero representation the character
must be trivial; the normalized absolute value then permits precisely exponent
zero. This is a derived boundary convention, rather than an additional result
quoted from the source. No rank-zero theorem is proved in this file.

`BernsteinPositiveCentralExponents T A` means that every member of that exponent
set is strictly positive. The zero object has no irreducible subquotients, so
its condition is vacuous. Existence and nonvanishing are separate obligations
when applying the predicate.

`bernsteinShiftedDerivative T ψ A k hk` is the actual Bernstein–Zelevinsky
order-`k` derivative followed by the actual determinant twist `ν^(1/2)`. This is
Bernstein's `A^[k]`. In particular the zero-order object is `ν^(1/2) A`, in
agreement with §7.2. At an order recorded by
`GeneralLinearHighestDerivativeOrderData`, the formula agrees with
`shiftedHighestDerivative` in `BernsteinUnitaryStatement`.

`BernsteinShiftedDerivativePositiveBelow T ψ A h` requires positivity at every
feasible order `k < h`, including `k = 0`. It records neither that `h` is highest
nor any property of the derivative at `h`. Those are separate inputs. For a
unitarizable highest shifted derivative, whose central exponents are zero,
this is the positivity comparison used in §8.2. It extends the lower-positive-
order inequalities of §7.4 by including order zero, as §8.2 explicitly does.
It does not define or assert the unrestricted comparison between two exponent
sets for an arbitrary highest derivative.

All representations, subquotients, derivatives and twists are actual Library
objects. The field and carrier universes are independent. Every field topology
and every unitary additive character are supplied explicitly.
