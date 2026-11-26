# Proof that arithmetic pullback preserves a unitary central character

Module `Langlands.Automorphic.ArithmeticComapUnitaryCentralCharacterProof`.

The theorem
`Langlands.Automorphic.arithmeticComapUnitaryCentralCharacter :
ArithmeticComapUnitaryCentralCharacterStatement.{uK, uL}` proves the published statement
`Langlands.Automorphic.ArithmeticComapUnitaryCentralCharacterStatement` (module
`Langlands.Automorphic.CuspidalArithmeticTransportStatement`), unchanged, at independent
field universes `uK` and `uL`. It uses no hypotheses beyond those of the statement and
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Statement proved

For number fields `K : Type uK`, `L : Type uL`, a ring isomorphism `e : K ≃+* L`, `r : ℕ`
and an irreducible cuspidal realization `S : CuspidalOperatorRealization L r`: if
`ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S`, that is, some
continuous character `χ` of the idele class group of `L` with `‖χ x‖ = 1` for all `x` is
a central character of `S`, then `HasUnitaryCentralCharacter (S.arithmeticComap e)`.

## The transported character

The theorem
`Langlands.Automorphic.CuspidalOperatorRealization.arithmeticComap_unitaryCentralCharacter`
names the witness. If `χ : HeckeCharacter L` satisfies `‖χ x‖ = 1` for all `x` and
`S.HasCentralCharacter χ`, then the pulled-back character
`HeckeCharacter.comap e χ` (module `Langlands.Global.HeckeCharacterTransport`) satisfies

- `‖HeckeCharacter.comap e χ x‖ = 1` for every idele class `x` of `K`, and
- `(S.arithmeticComap e).HasCentralCharacter (HeckeCharacter.comap e χ)`.

## The implemented proof

1. **Unitarity.** By definition `HeckeCharacter.comap e χ x = χ (ideleClassEquiv e x)`,
   where `ideleClassEquiv e` is the isomorphism of idele class groups induced by `e`
   (module `Langlands.Global.AdelicFunctoriality.Isomorphism`). So the norm condition at
   `x` is the hypothesis on `χ` at the idele class `ideleClassEquiv e x`; the proof term is
   `fun x => hχ (ideleClassEquiv e x)`.
2. **Central character.** The published theorem
   `CuspidalOperatorRealization.arithmeticComap_hasCentralCharacter_iff` (module
   `Langlands.Automorphic.OperatorArithmeticTransport`) states
   `(S.arithmeticComap e).HasCentralCharacter (HeckeCharacter.comap e χ) ↔
   S.HasCentralCharacter χ`. Its reverse direction gives the second clause.
3. **The target.** Given the hypothesis `HasUnitaryCentralCharacter S`, the proof takes
   its witness `χ` with its two properties and returns `HeckeCharacter.comap e χ` with the
   two clauses above.

This is the argument sketched in the statement's Markdown
(`Langlands/Automorphic/CuspidalArithmeticTransportStatement.md`, section
`ArithmeticComapUnitaryCentralCharacterStatement`). The same witness appears, for the
one-constituent isobaric data of `S` and with equal field universes, in
`Langlands.Automorphic.Unramified.isUnitary_arithmeticComap_ofCuspidal` (module
`Langlands.Automorphic.Unramified.WeakInductionTowerChain`).

## Source

The statement is a transport-of-structure interface, not a statement of the literature.
It is used silently in Harris (1998), *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134, 177–210 (registered source
`harris-1998-local-langlands`), proof of Proposition 4.8, printed p.203
(`math_9611226v1.tex`, lines 1646–1663). There the Galois conjugates `α^j(Π(e,t-1))`
of a cuspidal representation `Π(e,t-1)` are treated as cuspidal representations with
the corresponding properties, such as a supercuspidal component at the place above
`v(*)_1`. As the statement's Markdown records, unitarity of the central character of the
conjugates enters the same way. A Galois conjugate is the case `K = L`, `e = σ.symm` of
`arithmeticComap e`.
