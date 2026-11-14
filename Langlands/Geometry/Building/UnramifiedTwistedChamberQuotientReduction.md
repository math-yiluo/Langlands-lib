# Finite-field quotient data imply a generator-stable chamber

`UnramifiedTwistedChamberQuotientReductionStatement` is the implication from
`UnramifiedTwistedChamberQuotientStatement` to
`UnramifiedTwistedGeneratorChamberStatement`, at arbitrary universe `u`.
`unramifiedTwistedChamberQuotientReduction` proves this implication.

This is an internal assembly result. It uses the exact host building data,
coefficient action, finite-level cocycle and twisted-fixed point. It imposes
no additional hypothesis on them; its unproved input is the separately named
geometric quotient construction statement.

## Implemented proof

The theorem `unramifiedTwistedGeneratorChamber_of_quotient` installs the
actual residue-field algebra `(residueToFixedField F).toAlgebra` and its proved
algebraic-closure structure `fixedFieldResidueIsAlgClosure F`, with the same
finite enumeration used by the construction statement. Its algebraically
closed field instance is the `isAlgClosed` field of that algebraic-closure
structure. It obtains one dense
Galois generator `φ` and the finite-field quotient witnesses at the given
point `y`.

For the exact supplied coefficient action `A`, its published `action_smul`
identity and the group-action laws give

`c φ • A.action φ (g • z) = (c φ * φ(g) * (c φ)⁻¹) • (c φ • A.action φ z)`,

where `φ(g)` means `rationalConjugate F K G φ g`. This proves the required
semilinearity with the group twist that conjugates by `c φ`.

The proof then applies
`HasFiniteFieldChamberQuotient.exists_stable_chamber`. That theorem supplies
Lang surjectivity for the actual geometric points of the connected reductive
finite-field quotient, lifts a Lang correction through its surjective map,
and preserves the closure point because its acting subgroup fixes `y`.
It returns a chamber stable under the twisted action of this `φ`, together
with the exact translated generic-facet and closure-point witnesses.

The generator-chamber conclusion is formed with that same `φ`, its unchanged
density witness, the returned chamber, its stability equality and its retained
presentation. The explicit chamberhood result can be omitted because the
presentation already implies it. The final theorem is the same implication
packaged by the Prop-valued statement.

The construction input is not proved here. Passing from one generator to every
Galois automorphism is a separate reduction. This module does not prove the
host chamber target unconditionally or use any downstream cocycle-vanishing
or chamber consumer proof. No additional external result is restated.
