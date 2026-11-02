# Pullback of representation equivalences

For a commutative ring `R`, groups `Γ` and `Γ'`, representations `ρ` and
`σ` of `Γ`, an equivariant linear equivalence `e : ρ.Equiv σ`, and a
homomorphism `φ : Γ' →* Γ`, `equivComp e φ` is the same linear equivalence
between `ρ.comp φ` and `σ.comp φ`. Its equivariance is the original
equivariance equation evaluated at `φ g`.

This is the unchanged general helper moved from
[`HyperextDegenerationIsotypic`](../Cohomology/HyperextDegenerationIsotypic.md).
Its full name `Langlands.Cohomology.HyperextAbutment.equivComp`, quantified
type and implementation are preserved. That module and
[`FreeQuotientLimit`](../Cohomology/DivisibleSystem/FreeQuotientLimit.md)
share it; the latter's duplicate private helper has been removed.
This extraction introduces no new mathematical assertion.
