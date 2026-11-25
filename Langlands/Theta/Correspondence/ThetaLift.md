# The big theta lift and the statement of Howe duality

**GKT §13.3** (Definition 13.15, Proposition 13.16, p. 399; Definition 13.17, Proposition 13.18,
p. 400; Theorem 13.19, Definition 13.20, Theorem 13.21, p. 401), on the isotypic quotients of
GKT §13.2.2 (`Langlands.Representation.Smooth.IsotypicQuotient`).

The module `Langlands.Theta.Correspondence.ThetaLift` defines the big theta lift of a splitting of a
dual pair and states Howe duality for a representation of `G × H`.

## Content

- `MetaplecticGroup.Splitting.bigTheta s π = bigTheta s.weil π`: for a splitting `s` of
  `ι : G × H →* isometryGroup B` in the metaplectic group of pairs, the big theta lift
  `Θ_{ψ,s}(π) = (ω_{ψ,s} ⊗ π^∨)_G` (Definition 13.17), `ω_{ψ,s} = s.weil` (Definition 13.15).
- `ThetaMultiplicityOne ω`: Theorem 13.21 (1) without `Θ` and `θ`: every smooth irreducible `π`
  of `G` that is a quotient of `ω|_G` has a smooth irreducible `σ` of `H` with
  `dim Hom_{G×H}(ω, π ⊠ σ) = 1`, unique up to isomorphism among the smooth irreducible `σ'` with
  `Hom_{G×H}(ω, π ⊠ σ') ≠ 0`. `ThetaInjective ω`: Theorem 13.21 (2): `π ⊠ σ` and `π' ⊠ σ` both
  quotients of `ω` force `π ≅ π'`. `HoweDuality ω` is their conjunction.
- `finrank_hom_eq_finrank_bigTheta`: for an admissible `π` (and `G` with a cofinal family of compact
  open subgroups, `ω` smooth on `G`), `dim Hom_{G×H}(ω, π ⊠ σ) = dim Hom_H(Θ_ω(π), σ)` (Corollary
  13.8). Through it, `ThetaMultiplicityOne` says that `Θ_ω(π)` has a unique irreducible quotient
  `σ`, with `Hom_H(Θ_ω(π), σ)` one-dimensional; with the finite length of `Θ_ω(π)` (Theorem 13.19,
  not formalized) this is the book's form `dim Hom_H(θ(π), θ(π')) ≤ δ_{π,π'}` with
  `θ(π)` the maximal semisimple quotient (Definition 13.20).
- `swapRep ω`: `ω` as a representation of `H × G`; `restrictLeft_swapRep`; `homSwapEquiv`:
  `Hom_{H×G}(ω ∘ swap, σ ⊠ π) ≅ Hom_{G×H}(ω, π ⊠ σ)` (by `σ ⊗ π ≅ π ⊗ σ`). The book switches the
  roles of `G` and `H` in the same way (p. 401).

The small theta lift `θ(π)` (Definition 13.20) needs the finite length of `Θ(π)` (Theorem 13.19,
§16.4) and is not defined here; the statements are given in the equivalent form free of `θ`.

## Declarations

- `Langlands.Theta.ThetaMultiplicityOne`, `ThetaInjective`, `HoweDuality`.
- `Langlands.Theta.swapRep`, `restrictLeft_swapRep`, `homSwapEquiv`.
- `Langlands.Theta.finrank_hom_eq_finrank_bigTheta`.
- `Langlands.Theta.MetaplecticGroup.Splitting.bigTheta`.

## Dependencies

`Langlands.Representation.Smooth.IsotypicQuotient`, `Langlands.Theta.Metaplectic.Defs`; Mathlib:
`RepresentationTheory.Irreducible`.
