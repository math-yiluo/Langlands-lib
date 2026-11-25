# Integral inner-isomorphism torsors from supplied outer geometry

This internal construction works over any valuation domain `R` in universe
`u`, with a specified fraction field `K`. It takes an actual relative
full-centre quotient `q : G ⟶ A` with `IsRelativeAdjointQuotient q`, an
actual `GroupIsomorphismScheme G H`, and an `OuterIsomorphismScheme` for
its canonical inverse-precomposition action by `hq.innerAction`. For a
specified actual generic isomorphism `f`, it also takes a
`FiniteGenericOuterClass` containing the point that classifies the entire
natural local family `LocalGroupIso.ofBaseChangeIso f`.

`GenericInnerIsomorphismTorsor.ofOuter` constructs the exact published
`GenericInnerIsomorphismTorsor R K G H f` data. Its acting group is `A`;
the quotient and reductivity are the supplied ones. The relative quotient
interface provides its inner action, its restriction to conjugation, its
generic full adjoint quotient, and equality with the generic inner action.

Its parameter scheme is the actual outer fibre over `C.integralClass`.
The outer-fibre construction gives the categorical action, flatness,
surjectivity, quasi-compactness, and invertibility of the actual shear.
The local isomorphism is the universal family restricted to this fibre;
`fibreLocalIso_smul` supplies the required inverse-precomposition equation
on every test scheme.

The generic point is `C.genericFibrePoint`. The proof of `genericIso`
first uses `genericFibrePoint_localIso` to recover the family represented
by the original classified point. The representation inverse identity
`refine_classify` then recovers `LocalGroupIso.ofBaseChangeIso f`.
The published round-trip theorem
`toBaseChangeIso_ofBaseChangeIso` recovers exactly `f`.

All steps are internal consequences of the imported supplied-data
interfaces. This module makes no existence assertion for a relative
adjoint quotient, an isomorphism scheme, an outer quotient, or a finite
outer component. The unconditional
`GenericInnerIsomorphismTorsorExistenceStatement` is proved separately, as
`genericInnerIsomorphismTorsorExistence`
(`Reductive/GenericInnerIsomorphismTorsorExistenceProof`).
