# Reduction of `LeviSplitComponentStatement` to dynamic centralizer reductivity

Module `Langlands.GroupScheme.Rational.LeviSplitComponentReduction`.

## Statement

`leviSplitComponentStatement_of_dynamicCentralizerReductive` proves, for every universe `u`,

```
DynamicCentralizerReductiveStatement.{u} → LeviSplitComponentStatement.{u}
```

So `LeviSplitComponentStatement` (from `Rational.CharactersStatement`) follows from
`DynamicCentralizerReductiveStatement` (from `Dynamic.CentralizerReductiveStatement`). The
latter says: every closed group-scheme representative of the dynamic centralizer of a cocharacter
of a connected reductive group over a field is connected reductive.

The theorem proves neither proposition by itself. It reduces the first conjunct of
`LeviSplitComponentStatement`, connected reductivity of the dynamic Levi subgroup `M`, to the
hypothesis. The split-component conjunct is proved in full by the published
`leviSplitComponent_factorization`. Module `Rational.LeviSplitComponentProof` combines this
reduction with the published `dynamicCentralizerReductive` to prove
`LeviSplitComponentStatement`.

## Proof

Fix a field `k`, a connected reductive `G` over `Spec k`, a maximal split torus `i : T ⟶ G`, a
cocharacter `μ` of `T`, and a closed subgroup `j : M ⟶ G` representing
`Dynamic.centralizer (groupHom μ ≫ i)`.

- **First conjunct.** Apply the hypothesis to `G` and the cocharacter `groupHom μ ≫ i` of `G`,
  with the same closed representative `j`. This gives `IsConnectedReductive M`.
- **Second conjunct.** The field `isAffineHom` of `IsConnectedReductive G` gives the instance
  `IsAffineHom G.X.hom`. For a split component `iG : A_G ⟶ G`,
  `leviSplitComponent_factorization hT μ hjc hj hiG`
  (in `Rational.LeviSplitComponentFactorization`) then gives the required `A_M`, `iM`, `f` and
  `g`, together with the split-component property, the two factorization identities and the
  character-restriction identity.

## Provenance

This reduction is internal. It is derived from the two published statements and the published
factorization theorem. Their Markdown cites the mathematics: Renard, *Représentations des groupes
réductifs p-adiques*, V.3.6, for the Levi split-component statement, and Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, Proposition 1.2.4 and 2.1.8(3),(4), for reductivity of dynamic
centralizers.
