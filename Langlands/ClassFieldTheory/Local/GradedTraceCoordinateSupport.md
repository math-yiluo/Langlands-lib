# Divided traces and their residue coordinates

Author: Worker 96.

This internal support module constructs literal integral divided traces and
proves their residue linearization and coefficient nonvanishing from explicit
local trace-image hypotheses. It does not establish those hypotheses or the
closed prime graded-norm target. All integer rings, residue fields and maps
are the canonical ones of the supplied fields and algebra; the two field
universes are independent.

`dividedTrace` takes a bound carrying the trace of the source maximal ideal's
mth power into the target maximal ideal's nth power. It chooses the integral
trace witness and applies the existing `idealQuotient` construction. Its field
value is exactly `Tr(z) / piF^n`, as proved by `dividedTrace_coe`. The value is
therefore fixed even though its integrality certificate uses choice. Only the
target uniformizer is used in this construction; no total ramification or
Galoisness is needed.

For the remaining lemmas, assume the actual total-ramification identity
`e(L) = [L:F] * e(F)` and supplied order-one uniformizers in both fields.
`trace_coordinate_linear` additionally assumes that the trace of the
(m+1)st source ideal power is contained in the (n+1)st target ideal power.
For integral `c`, and integral representatives `b,q` with literal field values

- `b = Tr(piL^m) / piF^n`,
- `q = Tr(piL^m * c) / piF^n`,

it proves `r(residue(q)) = r(residue(b)) * residue(c)` in the source residue
field. Integrality of these supplied representatives is part of their types;
it is not asserted without hypotheses. Total ramification supplies residue-map
surjectivity. Lift the residue of `c` to an integer `a` in the base field.
Then `delta = c - image(a)` lies in the source maximal ideal, so
`piL^m * delta` lies in the (m+1)st power. The next-power trace bound implies
that its divided trace has zero residue. Field-trace linearity identifies
that quotient with `q - b*a`; reducing proves the formula.

`trace_coefficient_ne_zero` further assumes that every element of the nth
target ideal power is the trace of an element of the mth source ideal power.
Apply this to `piF^n` and divide a resulting source witness by `piL^m` to get
an integral coefficient `c`. The previous formula has left side one. A zero
residue of `b` would give `1 = 0`, proving nonvanishing. This argument includes
zero indices and does not infer nonvanishing merely from an order convention.

`trace_term_coordinate` specializes linearization to the literal unit
coefficient using the published exact identity
`piL^m * coefficient(x) = x - 1`. It retains arbitrary source and target
indices, and supplies the trace contribution only. None of the three residue
lemmas requires Galoisness or a prime-degree hypothesis; their local trace
bounds and total-ramification identity remain explicit.

The provenance is an internal generalization of the trace contribution in
Serre, *Local Fields* (1979), V.3, Proposition 5, printed pages 84–85
(PDF pages 91–92), cases (iii) and (iv) on page 85. The paper's residue-field
identification is expressed here by the actual forward relative residue map.
The 2019 author corrections, PDF pages 2–3, do not correct this passage.
The proof supplies linearization and nonvanishing separately from the
arithmetic trace-image theorem on which their applications depend.
