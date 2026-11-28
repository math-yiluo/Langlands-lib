# Constant terms commute with norm-one derivatives, in integrated form

Let `j : U ⟶ G` be a closed immersion of a smooth connected unipotent group over a number field and
`A` an embedded Lie atlas on `G(F∞)¹`. The module
`Langlands.Global.AdelicNormOneConstantTermDerivative` shows that the normalized constant term along
`U` preserves the integrated derivative identity `IsNormOnePathDerivative`
(module `Langlands.Global.AdelicNormOneFamilyDecay`), and that it preserves joint measurability of
families.

- `integrable_of_continuous_of_ae_mem`: a continuous function is integrable for a finite measure
  concentrated on a compact set.
- `unipotent_adelicPoints_mem_normOne`: the adelic points of `U` lie in `G(𝔸)¹`, because
  `U(F) \ U(𝔸)` is compact.
- `isNormOnePathDerivative_subgroupConstantTerm`: let `f` and `f' l` (`l : Fin e`) be continuous
  and left `U(F)`-invariant, and suppose `IsNormOnePathDerivative A f f'`. Then
  `IsNormOnePathDerivative A f_U (fun l => (f' l)_U)`.
  **Proof.** Write the constant terms as integrals against the measure `ν` of
  `exists_unipotentFundamentalMeasure`. For `y ∈ G(𝔸)¹`, a smooth path `c` with translated velocity
  `V` and `h` in the support, `h y` is again a norm-one point (`unipotent_adelicPoints_mem_normOne`),
  so the identity for `f` at `h y` gives
  `f(h y c(1)) − f(h y c(0)) = ∫₀¹ ∑_l V(t)_l f' l (h y c(t)) dt`. Integrate over `h` against `ν`
  and exchange the integrals over `h` and `t` (Fubini's theorem on `U(𝔸) × [0, 1]`; the integrand is
  continuous and bounded on the compact set `C × [0, 1]`).
- `measurable_subgroupConstantTerm_family`: for a jointly measurable family of continuous
  left `U(F)`-invariant functions, `(o, x) ↦ (f o)_U(x)` is jointly measurable, as the integral
  against `ν` of a jointly measurable function.
