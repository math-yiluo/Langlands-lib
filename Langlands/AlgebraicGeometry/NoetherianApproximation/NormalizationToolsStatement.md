# Normalization tools and the positive-characteristic case

`NormalizationToolsStatement` is the conjunction of four auxiliary assertions.
All ring and field universes are arbitrary. The finite-dimensional condition is
module finiteness of the indicated field extension.

1. Let `R` be a normal noetherian domain of finite type over the integers,
   let `K` be its fraction field, and let `L/K` be a finite extension with the
   specified compatible `R`-algebra structure. The integral closure of `R` in
   `L` is finite as an `R`-module. No separability condition is imposed on `L/K`.
2. Let `B` be a normal noetherian domain of finite type over the integers,
   and let `A` be a domain that is finite as a `B`-module with faithful
   `B`-scalar action. Then the integral closure of `A` in its own fraction
   field is finite as an `A`-module. The faithful action expresses the
   injectivity of the structural map `B → A`.
3. A domain of finite type over a finite field has finite normalization in
   its own fraction field.
4. A domain of finite type over the integers with prime characteristic `p`
   has finite normalization in its own fraction field.

These are internal intermediate assertions for the unconditional integer
finite type normalization task. Their provenance is the following algebraic
derivation from Mathlib's existing results, rather than an assertion that
general Nagata-ring stability has already been formalized.

For the first assertion, the separable closure `S` of `K` in `L` is a finite
separable extension of `K`, and `L/S` is purely inseparable of bounded exponent.
Mathlib's `IsIntegralClosure.finite` makes the integral closure of `R` in `S`
finite. A bounded Frobenius power gives an injective ring map from the closure
in `L` into the closure in `S`. Its composite with the scalar map is the
scalar map for the latter closure composed with a Frobenius power on `R`.
Such a power on a finite type integer algebra is finite: each target element
satisfies the monic polynomial `X^(p^n) - C x` through that map, and finite
type descends from the integer map. The resulting finite composite contains
the source closure as an `R`-submodule. Noetherianity makes that submodule
finite. In characteristic zero the exponential characteristic is one, so
the same construction uses the identity.

For the second assertion, the fraction fields form a finite extension.
Transitivity of integrality embeds the normalization of `A` into the
integral closure of `B` in that extension. The first assertion and
noetherianity imply module finiteness over `B`, hence over `A`.

For the third assertion, Mathlib's `exists_finite_inj_algHom_of_fg` supplies
a finite injective polynomial subbase over the coefficient field. This
polynomial ring is noetherian and a unique factorization domain, hence
normal. Its coefficient field is finite as an integer module, so the
polynomial subbase is of finite type over the integers. The second assertion
applies. For the fourth assertion, use the canonical algebra over the
finite prime field `ZMod p`; integer finite type implies finite type over
that field by restriction of scalars.

This file states these assertions and supplies no proof. In particular, it
does not supply a normal finite subbase for an arbitrary integer finite
type domain and does not prove the characteristic-zero part of
`IntegerFiniteTypeNormalizationStatement`.
