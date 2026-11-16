# Clauses 4–8 of the groups `G(K)_{x,r}` from the prerequisite statements

Helper module for Task 6191 (`LocalMoyPrasadGroupPropertiesStatement`). It collects
clauses 4–8 of that statement for fixed building data `B` over `K = F^ur` with
`Z = Z_G(S)` a torus (`hZ`). The inputs are two propositions (S1 and the statement of Task 6542) and two depth-zero
intersection facts. The module introduces no definitions.

## Inputs

- `hS1 : QuasiSplitLocalTorusFiltrationStatement` (S1, Task 5890). Only its first clause is
  used: the commutator friendliness of the torus filtration `Z(K)_r` (KP Definition 7.2.1).
- `hProd : LocalMoyPrasadPositiveProductStatement` (Task 6542). Assuming exactly that
  commutator clause, it gives the sign product cover at positive depth: for every `x`,
  every `r > 0` and every generic integral cocharacter `μ`,

  `G(K)_{x,r} = U_{Φ⁺(-μ),x,r} · j(Z(K)_r) · U_{Φ⁺(μ),x,r}` (as sets).
- `hDZa`: for every `x` and every generic integral `μ`,
  `U_{Φ⁺(μ)} ⊓ G(K)_{x,0} = U_{Φ⁺(μ),x,0}`.
- `hDZb`: for every `x` and every `ν ∈ V`,
  `M_ν ⊓ G(K)_{x,0} ≤ j(Z(K)_0) ⊔ U_{Φ⁰(ν),x,0}`.

`hDZa` and `hDZb` are, word for word, the two clauses at `F, H, B, hZ` of the published
proposition `LocalMoyPrasadDepthZeroStatement` (module `KPLocalMoyPrasadDepthZeroStatement`:
KP Proposition 7.3.12(1)–(3) and Lemma 8.5.19 at `f = 0`). This module does not import that
proposition and takes the two clauses as explicit hypotheses. Given
`hDZ : LocalMoyPrasadDepthZeroStatement`, they are `(hDZ F H B hZ).1` and `(hDZ F H B hZ).2`.

## Results

- `productCover_of_statements`: the sign product cover for `B`. It is `hProd` applied to
  `B`, with the first clause of `hS1` for `B` as its commutator premise.
- `intersectionClauses_of_statements`: from `hS1`, `hProd`, `hDZa` and `hDZb`,

  `LocalMoyPrasadRootIntersection B hZ ∧ LocalMoyPrasadIwahoriFactorization B hZ ∧`
  `LocalMoyPrasadLeviIntersection B hZ ∧ LocalMoyPrasadCentralizerIntersection B hZ ∧`
  `LocalMoyPrasadSeparated B hZ`.

  *Proof.* Let `hPC` be the product cover from `productCover_of_statements`. Each clause then
  comes from a companion module:
  - clause 4 from `rootIntersection_of_covers` (`hPC`, `hDZa`; module
    `KPLocalMoyPrasadIntersectionDepthZero`);
  - clause 5 from `iwahoriFactorization_of_productCover` (`hPC`; module
    `KPLocalMoyPrasadIntersectionLevi`);
  - clause 6 from `leviIntersection_of_covers` (`hPC`, `hDZb`; DepthZero module);
  - clause 7 from `centralizerIntersection_of_covers` (`hPC`, `hDZb`; DepthZero module);
  - clause 8 from `separated_of_productCover` (`hPC`; Levi module).

This module keeps its inputs explicit. The final composition in
`KPLocalMoyPrasadGroupPropertiesProof`, through
`KPLocalMoyPrasadGroupPropertiesReduction`, supplies them with the published
`quasiSplitLocalTorusFiltration`, `localMoyPrasadPositiveProduct` and
`localMoyPrasadDepthZero` theorems.
