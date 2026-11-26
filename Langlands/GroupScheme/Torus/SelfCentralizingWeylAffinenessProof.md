# Proof of the self-centralizing Weyl affineness statement

The theorem `Langlands.GroupScheme.selfCentralizingTorusWeylAffineness` proves
the proposition
[`SelfCentralizingTorusWeylAffinenessStatement.{u}`](SelfCentralizingWeylAffinenessStatement.md)
in every universe, with its statement unchanged: over an arbitrary base scheme,
a smooth separated quasi-compact group `G` with connected affine residue fibres
and a closed relative torus `t : T ⟶ G` which is fibrewise maximal and
represents its full centralizer has a smooth closed subgroup `N` representing
the normalizer and a separated quasi-compact étale Weyl quotient `q : N ⟶ W`,
flat, surjective and locally of finite presentation with kernel the torus on
every test scheme, and `G` is affine over the base exactly when `W` is.

## Proof

After introducing the data and recording smoothness, separatedness and
quasi-compactness of `G` as instances, the proof combines two results.

1. **Normalizer and Weyl quotient.** The theorem
   `exists_selfCentralizingTorusWeylQuotient` of the module
   [`SeparatedWeylQuotient`](SeparatedWeylQuotient.md) takes the proposition
   `SeparatedTorusNormalizerStatement.{u}` as a hypothesis; it is supplied by
   the theorem `separatedTorusNormalizer` (module
   `Langlands.GroupScheme.Torus.SeparatedNormalizerProof`). Applied to `G`,
   `t`, `RelativeTorus.IsTorus T.toGrp`, `IsClosedSubgroup t` and the
   centralizer hypothesis, it returns `N`, `n`, `W`, `q` with every existence
   conjunct of the target, in the target's order.

2. **Affineness criterion.** The theorem `isAffineHom_iff` of the module
   [`SelfCentralizingWeylAffinenessCriterion`](SelfCentralizingWeylAffinenessCriterion.md)
   takes the proposition `SelfCentralizingTorusConjugacyQuotientAffineStatement.{u}`
   as a hypothesis; it is supplied by the theorem
   `selfCentralizingTorusConjugacyQuotientAffine` (module
   `Langlands.GroupScheme.Torus.SelfCentralizingConjugacyQuotientProof`).
   Applied to all hypotheses of the target and to the data of step 1, it gives
   the last conjunct `IsAffineHom G.X.hom ↔ IsAffineHom W.X.hom`.

The anonymous constructor then assembles the existential.

## Sources

The statement follows SGA 3, Exposé XV, Proposition 7.1(iv) (existence of the
normalizer and the Weyl quotient) and Exposé XVI, Theorem 4.1(c)–(d) (the
affineness criterion); the source locators are recorded with the statement.
The criterion follows the source's route through the affine quotient `G/N`;
the Weyl quotient is constructed differently from the source, as described in
the Markdown of `SeparatedWeylQuotient`.
