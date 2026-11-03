# Finite-order extension from actual principal units

Worker 84 specifies the internal target
`Langlands.HarmonicAnalysis.PadicPrincipalUnitCharacterExtensionStatement.{u}`.
This module defines a proposition and contains no proof. The private derivation
adapts implementation details by Workers 394, 55 and 450, who are retained as
coauthors; the proof is a separate contribution.

For every prime p, every arbitrary-universe p-adic field F, every supplied
compatible topological realization T, every natural level n and every continuous
complex-unit-valued character eta of the actual subgroup T.principalUnits n,
there exists a continuous character chi on F.Carrier units. A single positive
natural exponent annihilates chi, chi agrees with eta on every subgroup
element, and chi has value one on the actual chosen uniformizer unit from
Langlands.LocalField.Uniformizer. The topology is exactly T.topology and the
induced units and subgroup topologies. Every prime including two and n=0 are
retained. No finite-order hypothesis on eta is necessary, and no particular
annihilating exponent is prescribed.

## Internal derivation

This is a consequence of the published conductor, normalization, uniformizer,
compact-unit and finite-quotient character-extension constructions. It is not
attributed to a separately numbered result of Henniart or Harris.

The principal-unit subgroup is open in the actual field-unit group, so it is
locally compact. The valuation topology makes it totally disconnected and
Hausdorff. Public Van Dantzig and the proved complex-character open-kernel
theorem therefore make ker(eta) open. Let K be the actual subgroup of units of
residue-normalized absolute value one. Principal units lie in K. Their inclusion
in K is continuous, injective and open, so the image N of ker(eta) is open in K.
The published compactness of K makes K/N finite. Its positive index m satisfies
x^m in N for every x in K. The public theorem
`Langlands.Topology.exists_character_of_open_finite_quotient` now extends eta
to a continuous character rho of K with rho^m=1.

The integer-valued normalized order is locally constant on field units. Thus
`P(a)=a*uniformizer^(-ord(a))` is a continuous multiplicative map into K. It fixes
every principal unit and sends the supplied uniformizer to one. Composing rho
with P supplies chi and preserves the same positive annihilating exponent.
All objects are actual field elements, units, subgroups and valuations; no
character-extension or splitting conclusion is supplied as extra data.

## Reuse and scope

The published IntegralUnitCharacterExtensionStatement concerns units of actual
number-field completions. This target instead covers every supplied p-adic
field and every principal-unit level, and requires no number-field realization.
The public generic finite-quotient extension theorem is reused; the new local
work constructs its open finite-index subgroup and the valuation splitting.
The principal-unit openness helper adapts Worker 394's implementation documented
in UnboundedConductorProof.md. The normalized-order continuity argument adapts
Workers 55 and 450's IntegralUnitCharacterExtensionProof to the supplied data.
Other published mathematical results are imported by Lean name.

This target supports extending the prescribed first-order character used in H2.
It asserts neither nontriviality nor a conductor bound, norm-trace compatibility
or an exact Galois stabilizer, and does not establish AuxiliaryCharacterStatement.
