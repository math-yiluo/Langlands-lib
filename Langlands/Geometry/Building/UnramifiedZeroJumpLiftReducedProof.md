# Proof of the zero-value lift of root jumps for non-multipliable relative roots

Module `Langlands.Geometry.Building.UnramifiedZeroJumpLiftReducedProof`.

## Result

`Langlands.Geometry.Building.unramifiedZeroJumpLiftReduced` proves the published proposition
`Langlands.Geometry.Building.UnramifiedZeroJumpLiftReducedStatement.{u}` (module
`Langlands.Geometry.Building.UnramifiedAffineRootRestrictionReduction`) at an arbitrary universe
`u`. Its type is exactly that proposition.

The statement is in the setting of `UnramifiedAffineRootRestrictionStatement`. `F` is a
nonarchimedean local field and `K = inertiaFixedField F`. `S` is a maximal split torus of `G`,
`T` a torus of `G` with `f : S → T` and `groupHom f ≫ iT = iS`, and `T_K` is a maximal split torus
of `G_K`. `x` is a point of the apartment of `D`, and
`φ x = torusFieldRestrictedRootFunctionFamily … (D.isRootDatumValuation_of_mem x.mem) f_K` is its
restriction to `(G, S)`. Let `α ∈ Φ(S)` with `2 • α ∉ Φ(S)`. Assume `α` has a filtration jump at
value `0` for `φ x`, that is, `U_{α,φx,0} ⊈ U_{α,φx,0+} · U_{2α}(F)`. Then some root `χ` of
`(G_K, T_K)` with `f_K ≫ χ = α_K` has a filtration jump at value `0` for `x.val`, that is,
`U_{χ,x,0} ⊈ U_{χ,x,0+} · U_{2χ}(K)`.

## Proof

The theorem is a specialization of the published
`Langlands.Geometry.Building.exists_rootJump_lift_of_two_nsmul_not_mem` (module
`RootJumpLiftNonMultipliable`). It is applied with `k = F`, `K = inertiaFixedField F`,
`i = iS`, `j = iT_K`, the valuation `x.val` with `hφ = D.isRootDatumValuation_of_mem x.mem`,
`f = f_K` and the level `r = 0`. Its jump hypothesis and conclusion use
`IsRootFiltrationJump`. By definition this is the expanded condition `¬ (… ⊆ … * …)` of the
statement, so the expanded hypothesis is accepted as is.

The lemma needs two inputs that the statement does not give directly.

- **Factorization over `K`.** The lemma needs `groupHom f_K ≫ iT_K = iS_K`. The proof gets it from
  `hf : groupHom f ≫ iT = iS` by rewriting with `← hf` and `Functor.map_comp`. The remaining goal
  says that the base change of `groupHom f` is `groupHom f_K`, and it holds by `rfl`.
- **Opposite factor pairs over `F`.** The lemma needs
  `RelativeRoot.HasOppositeFactorPairs iS`. The proof gets it for each relative root from
  `RelativeRoot.exists_oppositeFactorPair_of_componentReductivity`, applied to the published
  theorem `RelativeRoot.kernelCentralizerComponentReductive` and to `hG`, `hiS`.

The hypothesis that `x` is `Aut(K/F)`-fixed is not used, and neither are `C` or the
`IsOmegaCompatible` hypothesis.

**Elaboration detail.** The statement is a `def`, so Lean compiles the proofs nested in its
body, such as instance arguments and `hiS.isSplitSubtorus.1`, into auxiliary lemmas. After the
`let` binder `φ` is introduced, its values `φ x α g` are therefore not syntactically the lemma's
values. Matching them pointwise inside the set-builder of the jump hypothesis unfolds pullbacks
and exceeds the heartbeat budget. The proof avoids this: it first proves
`φ x = torusFieldRestrictedRootFunctionFamily …` with the lemma's explicit arguments
(`simp only [φ]`), rewrites the jump hypothesis with that equation, and then applies the lemma.
The module compiles at the default heartbeat limit.

## Role

This is one of the three inputs of
`Langlands.Geometry.Building.unramifiedAffineRootRestriction_of_zeroJumps`, which derives
`UnramifiedAffineRootRestrictionStatement` (Kaletha–Prasad, Proposition 9.4.28). The other two
inputs are `UnramifiedZeroJumpLiftMultipliableStatement` (the case `2 • α ∈ Φ(S)`) and
`UnramifiedZeroJumpDescentStatement`. Both still need a proof.
