# Proof of `LeviSplitComponentStatement`

Module `Langlands.GroupScheme.Rational.LeviSplitComponentProof`.

## Statement

`leviSplitComponentStatement : LeviSplitComponentStatement.{u}` proves the published statement
`Langlands.GroupScheme.LeviSplitComponentStatement` (module
`Langlands.GroupScheme.Rational.CharactersStatement`) at an arbitrary universe `u`, with all of
its hypotheses and nothing more.

Over every field `k`, let `G` be connected reductive, `i : T ⟶ G` a maximal split torus, `μ` a
cocharacter of `T`, and `j : M ⟶ G` a closed subgroup representing the dynamic centralizer of
`μ ≫ i`. Then:

1. `M` is connected reductive;
2. for every split component `iG : A_G ⟶ G` there are a split component `iM : A_M ⟶ M` and
   homomorphisms `f : A_G ⟶ A_M` and `g : A_M ⟶ T` with `f ≫ iM ≫ j = iG` and
   `g ≫ i = iM ≫ j`, and the restrictions `X^*(G)_k → X^*(M)_k → X^*(A_M) → X^*(A_G)` compose to
   `characterRestrict iG`.

The theorem covers every closed representative `j` and every cocharacter, including the zero
cocharacter. No splitness, perfectness or characteristic hypothesis is added, and neither
reductivity of `M` nor a factorization is assumed.

## Proof

The proof is one term:

```
leviSplitComponentStatement_of_dynamicCentralizerReductive dynamicCentralizerReductive
```

- `leviSplitComponentStatement_of_dynamicCentralizerReductive` (module
  `Rational.LeviSplitComponentReduction`, new in this contribution) shows
  `DynamicCentralizerReductiveStatement.{u} → LeviSplitComponentStatement.{u}`. It gets
  conjunct 1 by applying the hypothesis to `G`, the cocharacter `groupHom μ ≫ i` of `G` and the
  same closed representative `j`. It gets conjunct 2 from the published
  `leviSplitComponent_factorization` (module `Rational.LeviSplitComponentFactorization`), after
  taking `IsAffineHom G.X.hom` from the `isAffineHom` field of `IsConnectedReductive G`. Its
  paired Markdown gives the details.
- `dynamicCentralizerReductive : DynamicCentralizerReductiveStatement.{u}` is the published
  theorem of module `Dynamic.CentralizerReductiveProof`. Over an arbitrary field, every closed
  representative of the dynamic centralizer of a cocharacter of a connected reductive group is
  connected reductive.

A closing `example` checks the type `LeviSplitComponentStatement.{u}` of the theorem.

## Provenance

This proof is internal. It combines the published theorems `dynamicCentralizerReductive` and
`leviSplitComponent_factorization`. The mathematics follows Renard, *Représentations des groupes
réductifs p-adiques*, V.3.1 and V.3.6, as cited by the statement's Markdown. The proofs of
reductivity of dynamic centralizers and of the split-component factorization follow their own
routes, described in their paired Markdown.
