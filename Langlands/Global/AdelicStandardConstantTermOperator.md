# Constant terms along standard unipotent radicals as `L²` contractions

Module `Langlands.Global.AdelicStandardConstantTermOperator`, namespace
`Langlands.Global.StandardConstantTerm`.

## Statement

`StandardConstantTermOperatorStatement`, proved by `standardConstantTermOperator`. The setting:

- `G` is connected reductive over a number field `F`, `i : T → G` is a maximal split torus,
  `ν` is a generic cocharacter, and `J ⊆ Δ₀`.
- `Λ₀ = minimalParabolicImage F G i ν` is the image of `P₀(F)` in `G(𝔸)`, and `D` is the
  Library's Borel fundamental domain of `Λ₀` (`LeftCosetSpace.fundamentalDomain`).
- `W : G(𝔸) → [0, ∞]` is measurable with `W(l x) = W(x)` for `l ∈ Λ₀` and `W(w x) = W(x)` for
  `w ∈ U_J(𝔸)`.

Put `μ_W = (μ|_D).withDensity W`, where `μ` is Haar measure on `G(𝔸)`. Then there is a
continuous linear operator `T` on `L²(μ_W)` with `‖T‖ ≤ 1`. For every class `F` and every
measurable `f` that agrees with `F` almost everywhere, `T F` agrees almost everywhere with
`foldConstantTerm … f`: the function `g ↦ ν(C)⁻¹ ∫_C f(fold(v g)) dν(v)`, where `C` is the
fundamental domain of `U_J(F)` in `U_J(𝔸)`, `ν` is Haar measure on `U_J(𝔸)`, and `fold` moves a
point of `G(𝔸)` into `D` by an element of `Λ₀`.

For `W = w_λ⁻² · 1_S`, with `w_λ` and the Siegel domain `S` depending only on the Iwasawa height
(which is invariant under `P₀(F)` and under `U_J(𝔸) ⊆ N₀(𝔸)` on the left), `L²(μ_W)` is the
fundamental-domain model of Bernstein–Lapid's weighted space. `T` is then `CT_{P_J}` of
Bernstein–Lapid, J. Amer. Math. Soc. 37 (2024), §7.3, p.214, as a contraction.

## Proof

The structural facts of `Langlands.Global.AdelicStandardConstantTermIntegral` (closedness and compact
quotient for `U_J`, `U_J(F) ⊆ Λ₀`, normalization) and the Haar facts of
`Langlands.Global.AdelicConstantTermAverage` (right invariance from the compact quotient, hence
inversion invariance, and invariance under conjugation by `Λ₀`) are exactly the hypotheses of
`Langlands.Analysis.FibreAverage.foldConstantTermOperator`, which is then applied.

## Scope

Only the operator for one `J` is constructed. Idempotence, the composition rule
`CT_R CT_Q = CT_{R ∩ Q}`, commutation with translations, the choice of `W` and local
finiteness are not proved here.
