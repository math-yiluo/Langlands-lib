# Integral sections and finite carriers of outer classes

Worker 635.

These are internal consequences of the supplied outer-class interface
and the published extension of generic points in finite schemes over
valuation rings. They require neither reductivity nor existence of an
outer quotient: the quotient is an input.

Over any base scheme, `FiniteGenericOuterClass.ofIntegralClass` takes an
integral section whose restriction has the specified outer class and
uses the base itself as the finite carrier. Its structural morphism is
the identity, hence finite. `ofFiniteParameter` uses the entire outer
parameter when its structural morphism is finite. It makes no assertion
that arbitrary outer parameters have this property.

`ofClassEq` retains a carrier, its class morphism and its prescribed
point when a second point has the same outer class.
`nonempty_iff_of_class_eq` applies this construction in both directions.

For a commutative domain valuation ring with specified fraction field,
`nonempty_iff_exists_integralClass` characterizes finite-carrier
existence by extension of the prescribed generic outer class to a
section over the base. The forward implication is the existing
`FiniteGenericOuterClass.integralClass` and its exact generic equality,
proved using the valuative criterion for finite morphisms. The reverse
implication is `ofIntegralClass`. No uniqueness is asserted for the
integral outer class, since separatedness of the outer parameter is not
assumed. The theorem does not supply the section or prove the target
finite-carrier existence assertion for reductive groups.
