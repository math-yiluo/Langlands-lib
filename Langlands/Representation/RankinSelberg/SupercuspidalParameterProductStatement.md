# Original and dual supercuspidal parameter products

`SupercuspidalParameterProductStatement` is an internal consequence of the
equal-rank supercuspidal L-factor formula and smooth-duality transport. It
quantifies over a p-adic field, a unitary additive character, its supplied
self-dual Haar measure, and two representations of the same positive
general-linear rank. The first is irreducible and supercuspidal; the second
is irreducible and of Whittaker type for the standard character. The field
and the two representation carriers have independent universes.

The conclusion supplies a finite set `A` of nonzero complex numbers,
represented as complex units. Its membership is exactly the existing
`IsContragredientTwistParameter` predicate. The polynomial
`∏ a ∈ A, (1 - a X)` is certified for the original pair. The polynomial
`∏ a ∈ A, (1 - a⁻¹ X)` is certified for the actual inverse-transpose pullbacks,
with the negated additive character and the same underlying Haar measure.
If both original representations are unitarizable, every parameter in `A`
has norm one. Unitarizability is a premise of this last clause only.

The provenance is internal: the equal-rank formula supplies the finite
parameter set, whose elements are nonzero. Smooth contragredient duality
inverts its parameters; Gelfand--Kazhdan identifies these duals with the
inverse-transpose pullbacks. The latter preserve supercuspidality and
Whittaker type with reversed character, so the equal-rank formula applies
again. The existing unitary parameter estimate gives the final norm clause.
This statement neither proves the equal-rank formula nor identifies any
centered segment component or its L-polynomial.
