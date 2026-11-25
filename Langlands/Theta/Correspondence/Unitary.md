# Howe duality for the unitary dual pairs with `W` split: the statement

**GKT Theorem 13.21** (Howe duality, p. 401) for the Weil representation `ω_{ψ,s} = ω_ψ ∘ s`
(Definition 13.15, p. 399) of the unitary dual pair `(U(ν, ν), U(Q))` of Case `3₊` with `W` split,
with the Leray splitting of the pair (Definition 12.20, p. 365) for the data `(χ, ψ)` and `μ = 1`.

The module `Langlands.Theta.Correspondence.Unitary` states Howe duality for these pairs as a
`Prop`. Nothing is proved about the statement here.

## Content

- `HoweDualityUnitarySplitStatement`: for every quadratic extension `E / F` of nonarchimedean local
  fields of characteristic zero (`hE : IsQuadraticInvolution c δ`), every invertible Hermitian
  `Q ∈ M_α(E)`, every continuous `χ : Eˣ →* Circle` with `χ|_{Fˣ} = χ_{E/F}^{|α|}` and every
  non-trivial unitary character `ψ` of `F`, the Weil representation
  `pairWeil c ν ψ χ Q hE hQ hQu hχ hres` of `U(ν, ν) × U(Q)`
  (`Langlands.Theta.DualPair.Unitary.Pair`) satisfies `HoweDuality`
  (`Langlands.Theta.Correspondence.ThetaLift`: parts (1) and (2) of Theorem 13.21, free of `θ`).
- `howeDualityUnitarySplit_weil_pairSplitting`: the representation is the Weil representation of
  the splitting `pairSplitting` of the pair in the metaplectic group of pairs.

The case of a non-split `W` (GKT §11.4) and the other members of Case `3` are not covered: the
Library has the Weil representation only for `W` split.

## Declarations

- `Langlands.Theta.HoweDualityUnitarySplitStatement`,
  `Langlands.Theta.howeDualityUnitarySplit_weil_pairSplitting`.

## Dependencies

`Langlands.Theta.Correspondence.ThetaLift`, `Langlands.Theta.DualPair.Unitary.Pair`.
