# Descent of `(G, M)`-families to a special subspace

`Langlands.GMFamily.specialDescentFormula` proves the descent identity of J. Arthur, *The invariant trace formula. I. Local theory* (1988), §7, Proposition 7.1, printed p.357 (PDF p.35), `arthur-1988-invariant-trace-formula-I`, in the Euclidean model of [GMFamilies](GMFamilies.md). Its hypotheses are a root set `R`, a Levi flat `a₁`, a subspace `a ⊆ a₁` containing the central space of `R` that is special for positive weights (`IsSpecialSubspace`, see [GMFamilySliceSpecial](GMFamilySliceSpecial.md)), a `(G, M₁)`-family `c₁` on `a₁`, and a displacement `ξ ∈ a₁ ∩ aᗮ` such that every transverse Levi flat with nonzero descent coefficient meets the displaced coarse space at a regular point. For every parameter `Λ` on `a` that is nonzero on every nonzero restriction of a root to `a`,

```
cM R a (inducedFamily R a a₁ c₁) Λ =
  ∑ L ∈ leviSpaces R a₁, dDescent a (centralSpace R) a₁ L ·
    cQM R a₁ c₁ (descentSection R a (centralSpace R) ξ L) (extendParam a a₁ Λ).
```

The coarse space need not be a Levi flat. This is the situation of a Levi subgroup over an extension field inside a Levi subgroup over the ground field (Arthur, *An introduction to the trace formula* (2005), Lemma 17.5, printed pp.99–100, `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`).

## Proof

`CentralSubspaceDescent.cM_induced_eq_descentSum` in [GMFamilyCentralSubspaceDescent](GMFamilyCentralSubspaceDescent.md) proves the identity for every coarse subspace containing the central space, given the values of the vertex sums of the fine chambers over the coarse chambers (`CentralSubspaceDescent.HasLiftVertexSums`). For a special subspace these values are `vertexSum_eq_of_special_extension` of [GMFamilySliceSpecial](GMFamilySliceSpecial.md): the reciprocal coarse denominator for the lift selected by the displacement and `0` for the other lifts. `hasLiftVertexSums_of_special` records this, and `specialDescentFormula` assembles the descent position from the hypotheses.
