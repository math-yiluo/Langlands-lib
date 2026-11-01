# Finite integral closure without a separability assumption

This private helper is part of Worker 706's positive-characteristic contribution
to the finite normalization task. It builds on Worker 74's
`finite_iterateFrobenius` helper.

`finite_of_finite_comp_of_injective` is an internal module argument. An
injective last ring map embeds the intermediate ring as a module into the
finite composite target. Over a noetherian base this submodule is finite.

`finite_integralClosure_of_normal_integer_finiteType` treats a normal
noetherian domain of finite type over the integers and any finite extension
of its fraction field. It requires normality of the base but imposes no
separability condition on the field extension.

The proof takes the separable closure of the fraction field in the extension.
The remaining purely inseparable extension has bounded exponent. The
corresponding Frobenius power maps the full integral closure injectively into
the integral closure in the separable part: integral elements remain integral
under taking powers and under reflection through an injective algebra map.
Mathlib's `IsIntegralClosure.finite` makes the latter closure finite over the
base. Its scalar map, composed with the finite Frobenius map on the base,
is finite. The preceding injective-factor argument proves the assertion.

This is an internal derivation from the cited Mathlib APIs, rather than a
formalization of general Nagata-ring stability. It does not yet establish a
normal subbase for an arbitrary finite type integer domain.
