# Holomorphic jets of principal-series functions

Fix exponents `σ : Fin n → ℂ`. With the Gram weights `T_m = gramWeight m` (Gram determinant of the
rows `m, …, n-1` of `nbMat v`), `ω = ∏_m T_m^{σ_m}` and `D = ∏_m T_m`:

## Definitions

- `antiIncl`, `nbHol`, `nbAnti`: the holomorphic and antiholomorphic formal copies of `nbH`;
  `gramF m`: the Gram determinant `det(Y_m Ȳ_mᵀ)` of the rows `m, …` as a formal real polynomial;
  `gramProdF = ∏_m gramF m`; `evalAt v`: evaluation at `(v, v̄)` as a ring hom.
- `JetRel σ F N P`: `F(nbUnit v) D(v)^N = ω(v) · evalC P v` for all `v`.
- `HasJet σ F Q`: for some `N` and `P` with `JetRel σ F N P`, `Q = ιP (holPart P)`.

## Results

- `evalC_gramF`: `evalC (gramF m) = gramWeight m`; `evalC_gramProdF`.
- `holPart_gramF`, `holPart_gramProdF`: with `v̄ = 0` the Gram determinants become `1` (the rows
  `m, …` of `nbH` restricted to the columns `m, …` form a lower unitriangular block,
  `det_nbH_submatrix`).
- `JetRel.lift`, `holPart_lift`: raising `N` multiplies `P` by `D` and keeps `holPart P`.
- `HasJet.unique`: the jet is unique (`evalC_injective`, since `ω ≠ 0`).
- `HasJet.add`, `HasJet.smul`, `hasJet_zero`, `HasJet.sum`: jets are linear.

## Provenance

Internal infrastructure for the proof of `ComplexStandardHolomorphicGrowthStatement`
(Library module `ComplexLinkedLanglandsQuotientGrowth`); see
`ComplexStandardHolomorphicGrowthProof.md` for the overall argument. The module introduces no
statement from the literature, and all its results are proved here.
