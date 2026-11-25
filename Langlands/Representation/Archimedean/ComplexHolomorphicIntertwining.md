# Holomorphic right derivatives act on jets

Let `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}`.

## Definitions

- `holDeriv X F = ½ (R(X) F - i R(i X) F)`, the holomorphic right derivative (the action of
  `hol X`).
- `alphaOf l t k = l_k / 2 + t_k + (n-1)/2 - k`.
- `dW X P = Σ_k holIncl (fieldWH X k) · ∂_{(k, false)} P`, the formal holomorphic derivative along
  the vector field `W_X`.

## Results

- `conjMat_I_smul`, `fieldW_I_smul`, `torusDeriv_hol`: `conjMat (iX) = i conjMat X`,
  `fieldW (iX) = i fieldW X`, and `½(Λ(d) - iΛ(id)) = Σ_k α_k d_k` for the torus derivative `Λ`.
- `rightDerivative_nbUnit` (from `rightDerivative_nbMat` and
  `fderiv_unitsExtension_diagonal_mul`) and `holDeriv_nbUnit`: for `F` in the principal series of
  `χ`, `holDeriv X F (nbUnit v) = (Σ_k α_k conjMat X v k k) F(nbUnit v) + wirt φ v (fieldW X v)`
  with `φ = F ∘ nbUnit`; `differentiable_nbUnit_comp`.
- `evalC_dW`, `holPart_dW`, `holPart_dW_eq_zero_of`, `ιP_pderiv`.
- `hasJet_holDeriv`: if `F` is in the principal series of `χ` and has jet `Q`, then
  `holDeriv X F` has jet `op (opDataH (alphaOf l t) X) Q`. Proof: by `wirt_weighted_apply`,
  `holDeriv X F (nbUnit v) D^{N+1} = ω · evalC P'` with
  `P' = λ_X P D + Q_W P + D · dW X P - N P · dW X D` (all formal); setting `v̄ = 0` kills the
  derivatives of the Gram weights and of `D` (`holPart_gramF`), leaving
  `λ_X Q + Σ_k W_{X,k} ∂_k Q`.

## Provenance

Internal infrastructure for the proof of `ComplexStandardHolomorphicGrowthStatement`
(Library module `ComplexLinkedLanglandsQuotientGrowth`); see
`ComplexStandardHolomorphicGrowthProof.md` for the overall argument. The module introduces no
statement from the literature, and all its results are proved here.
