# Finite Banach algebras have actual weighted affinoid presentations

This derived construction proves the presentation step needed by finite
Banach algebra descent. For a presented positive-polyradius affinoid algebra
`A`, a complete ultrametric normed commutative `K`-algebra `B` whose unit has
norm at most one, and an actual finite Banach bounded map `f : A → B`,
`FiniteBanachPresentation.exists_presentation` gives a presented affinoid
algebra boundedly equivalent to `B` with its supplied norm.

The source is Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), printed p.25 / PDF p.39, immediately before
Proposition 2.1.12: a finite Banach algebra over an affinoid algebra is again
affinoid. Registered source:
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The explicit unit-norm assumption is sufficient for the implemented relative
evaluation API; it is proved for the actual matching algebra in this module.
The general theorem here is stated only with that assumption.

Given the finite Banach generating tuple `b`, choose radii `‖b i‖ + 1` and
form the existing unconstrained weighted adjunction over the supplied
presentation of `A`. The existing relative-series map takes this actual
quotient to weighted series over `A`. The original bounded coefficient map
`f` induces the existing coefficientwise bounded series map to series over
`B`. Evaluation at `b` now uses the identity coefficient map of `B`, which is
contractive. The norm bounds on `b` and on the unit give the required
weighted monomial estimates. Thus the original `f` needs only its supplied
boundedness, with no extra contractivity assumption.

The evaluation sends the original coefficient algebra by `f` and the new
coordinates to `b`. The linear polynomial associated to a coefficient tuple
`c` therefore maps to `f.coefficientMap b c`. Its source norm is bounded by
`((∑ i, (‖b i‖ + 1)) + 1) * ‖c‖`. Combining this with the supplied positive
uniform finite Banach lift bound gives norm-controlled preimages for the
actual evaluation. The admissible-epimorphism criterion then proves the
map is admissible. Its kernel is closed by continuity. The existing
`ClosedQuotient.equivOfAdmissibleEpi` constructs a presented closed quotient
and a bounded equivalence to `B`, with bounded inverse coming from the
controlled preimages.

For the actual matching algebra, `norm_one_matching_le` follows componentwise
from the quotient unit bounds using the finite maximum norm. Consequently
`matchingPresentationOfFinite` constructs the exact `MatchingPresentation`
from norm-controlled finiteness of the original matching structural map.
No affinoid matching presentation is assumed as an input.

The finite tuple may be empty. The added one in the polynomial bound keeps
the bound positive in that case. Zero quotients and empty products are
included. The coefficient field may be trivially valued and all radii are
arbitrary positive real numbers. The proof uses controlled preimages and
does not infer finite Banach structure from algebraic module finiteness or
use an open mapping theorem.
