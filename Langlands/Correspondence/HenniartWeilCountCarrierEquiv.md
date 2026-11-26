# Changing the carrier universe in Weil orbit counts

`Langlands.Henniart.LocalNumerical.weilRefinedStratumCarrierEquiv`
identifies the actual unramified-twist orbit strata at any two
representation carrier universes. The local field \(K\), its separable
closure \(\Omega\), the positive rank, Swan exponent and torsion number
are fixed. The field and closure universes are independent of both
carrier universes. The result applies in both characteristics.

The coordinate-model equivalence on continuous irreducible classes
preserves each rank and commutes with character twists. The orbit
equivalence `unramifiedOrbitCarrierEquiv` therefore carries a Weil
orbit to the orbit of the corresponding class. The character parameters
that fix a Weil class are unchanged, by equivariance and injectivity
of the class equivalence.
[Orbit carrier equivalence](../VirtualRepresentation/Weil/OrbitCarrierEquiv.md)

To carry an Artin conductor witness across, the proof takes equivalent
representatives at the two carrier universes. It restricts their
intertwiner to Weil inertia and uses the same finite Galois subextension
in the two finite inertia presentations. `kernel_le_of_equiv` transports
the kernel condition. `artinConductorOfQuotient_equiv` then gives equality
of the rational Artin expressions. Subtracting the common rank in
the natural numbers yields the same Swan relation. This works with
the given conductor witnesses, including Swan exponent zero.

The orbit equivalence preserves and reflects membership in the refined
stratum by carrying a witnessing class forward or taking its preimage.
Restricting the equivalence gives equality of extended cardinalities in
`ℕ∞`. Torsion number one gives `weilTwistIrreducibleCount_carrierEquiv`.
Summing these equalities gives `weilConductorCount_carrierEquiv`.

These comparisons are derived from the class and presentation
equivalences. The numerical quantities come from Henniart (1988),
`henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§1.3, p. 498 and Proposition 2.2, p. 504. The refined strata and the
sum including Swan exponent zero follow the numerical route note
`operator-numerical-llc-route-2026-11-16`, directory SHA-256
`faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`,
`numerical-LLC-route.tex`, §§2.2–2.3, lines 182–216.
[Weil-side counts](HenniartLocalNumerical.md) ·
[Carrier equivalence](../Weil/Representation/ContinuousIrreducibleCarrierEquiv.md) ·
[Finite inertia descent](../LocalFactor/Ramification/Descent.md)
