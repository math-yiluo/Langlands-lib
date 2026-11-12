# Inverse supplied residue powers and valuation congruences

Worker 91 authors this derived proof of the published
`Langlands.LocalClassField.NYLL.SuppliedInverseResiduePowerStatement.{u, v}`.
The theorem is `Langlands.LocalClassField.NYLL.suppliedInverseResiduePower`.
Its type is exactly that proposition, with independent arbitrary carrier
universes `u` and `v`.

The proof first establishes the equivalence on a representative
`x : TE.Integers`. Since the actual supplied residue action
`Ramification.Padic.residueHom TE F.Carrier` is a group homomorphism,
`map_inv` identifies the inverse of its value at `σ` with its value at
`σ⁻¹`. By the definitions of the action and the residue quotient, this
sends `TE.residue x` to the residue of
`Ramification.Padic.integerAutomorphism TE F.Carrier σ⁻¹ x`.
The latter integral element has underlying field element `σ.symm x`.
Rewriting the power with `map_pow`, the published
`suppliedResidueCongruence E TE` gives exactly
`TE.discreteValuation (σ.symm x - x ^ q) < 1`.

For the forward implication,
`TE.mem_integers_iff_discreteValuation_le_one` makes any field element of
valuation at most one into an element of the supplied integer ring. The
assumed power action and the representative equivalence give its valuation
congruence. For the reverse implication,
`IsLocalRing.residue_surjective` supplies an integral representative of any
residue class. Its membership in the integer ring gives the required
valuation bound by the same membership theorem, and the representative
equivalence gives the power formula.

This is an internal consequence of existing Library constructions, the
published supplied residue congruence theorem, and Mathlib's group
homomorphism and residue quotient interfaces. It uses the actual supplied
data throughout. It requires no abelian or Galois hypothesis, no supplied
base realization, and no additional compatibility assumption. The exponent
is any natural number, including zero. No Artin map or reciprocity theorem
is used. The target's Lean/Markdown pair and import closure are unchanged.

The approved environment is
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, with Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
