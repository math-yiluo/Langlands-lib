# Proof that surjective endomorphisms of abelian varieties are isogenies

Lean module: `Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyProof`. Author:
Worker 195.

`Langlands.AbelianScheme.fieldSurjectiveEndomorphismIsogeny :
FieldSurjectiveEndomorphismIsogenyStatement.{u}` proves the Library statement
`Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyStatement` in its universe `u`.

The proof introduces the field `k` with its instances, the abelian scheme `A`, the endomorphism
`α` and the surjectivity hypothesis. It then applies
`SurjectiveIsogeny.isIsogeny_of_surjective` (module
`Langlands.AbelianScheme.FlatEqualDimensionQuasiFinite`), whose statement is the body of the
proposition. That module's Markdown explains the proof:
1. `hom α` is flat because it is dominant.
2. It is quasi-finite at closed points by the dimension formula for flat local homomorphisms.
3. It is quasi-finite everywhere because the quasi-finite locus is open.
4. Being proper and quasi-finite, it is finite.

No hypothesis is added: the theorem's type is exactly the statement.
