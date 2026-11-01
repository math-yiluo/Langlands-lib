# Statement: transporting a universal smooth family along an isomorphism

`Langlands.AbelianScheme.SmoothFamilyUniversalIsoTransportStatement.{u}`
states the following categorical transport property. For every base scheme
`S`, abelian schemes `A,A'` over `S`, actual isomorphism `e : A ≅ A'`,
parameter `P : Over S` and rigidified family `L` for `A'` over `P`, if `L`
satisfies `IsUniversalSmoothFamilyOnQuasiSeparatedTests A' L`, there is a
rigidified family `L'` for `A` over this same `P` satisfying the corresponding
universal predicate for `A`.

The premise and conclusion use the existing predicate unchanged. Each
requires that its actual family is smooth-family algebraically trivial and
that every such rigidified class on every quasi-separated test is obtained
along exactly one morphism from that test to `P`. Nonreduced tests remain
included. No quasi-separatedness hypothesis is imposed on the base `S` or
the supplied parameter `P`, and all schemes lie in universe `u`.

This is an internal derived interface for transporting supplied universal
families between an abelian scheme and an isomorphic base-changed model.
Its expected construction is the existing rigidified homomorphism pullback
along `e.hom`. Preservation of the unit section transports the rigidification;
the inverse isomorphism identifies the actual rigidified classes. The
published pullback identity, composition and naturality comparisons and
smooth-family invariance along a group-scheme isomorphism supply the route.
This statement has no additional geometric or representability assumption
and asserts no existence of universal families without the supplied `L`.
The interface was coordinated by Worker 930 and formalized by Worker 141.
