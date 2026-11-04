# Coefficients of group algebras over `Λ × Λ`

Author: Worker 1387.

This internal helper module, in the namespace
`Langlands.GroupScheme.CentralSurjectionImage`, records coefficient formulas
for group algebras `S[Λ] = AddMonoidAlgebra S Λ`, where `S` is a commutative
`k`-algebra and `Λ` an additive commutative group, all in one universe `u`.
They are used to compare multiplicativity of points over `S[Λ]` with
convolution identities.

- `diagonal Λ` is the additive map `γ ↦ (γ, γ)` from `Λ` to `Λ × Λ`. It is the
  same term as `CocharacterDatum.diagHom Λ`.
- `coeff_mapDomain_diag`: the `(γ, δ)`-coefficient of the image of `x` along the
  diagonal is `x.coeff γ` if `γ = δ` and `0` otherwise. For `γ = δ` this is
  `Finsupp.mapDomain_apply_of_injective`; otherwise `(γ, δ)` is not in the range
  of the diagonal (`Finsupp.mapDomain_of_notMem_range`).
- `coeff_mapDomain_inl_mul_inr`: for `x y : S[Λ]`, the product of the images of
  `x` and `y` along the two inclusions `Λ → Λ × Λ` has `(γ, δ)`-coefficient
  `x.coeff γ * y.coeff δ`. The proof is induction on `x` and on `y` with
  `AddMonoidAlgebra.induction_linear`; on monomials it is
  `single (a, 0) r * single (0, c) t = single (a, c) (r * t)`.
- `coeffL k γ` is the `γ`-coefficient as a `k`-linear map `S[Λ] → S`.
- `coeff_productMap_inl_inr'`: for an algebra map `c : B → S[Λ]` and
  `t : B ⊗[k] B`, the `(γ, δ)`-coefficient of
  `productMap (inl ∘ c) (inr ∘ c) t` is the contraction
  `mul' ((coeffL γ ∘ c) ⊗ (coeffL δ ∘ c)) t`. The proof is induction on `t`, the
  pure-tensor case being the previous lemma.

These are elementary, internally derived facts about group algebras; no
literature result is attributed to them.
