# Naturality of the c-family in the inducing representation

This module proves that the c-map of `RationalWeakExpansionCFamily` commutes with equivalences of
the inducing representation. Let `B` and `B'` be smooth representations of the standard Levi
subgroup `M_I(F)` and `b : B ≃ B'` an equivalence of representations. The module transports
`b` through every step of the construction of `c_{P'|P}(s, ·)`.

## Coefficient tensors and compact pictures

- `contragredientEquivOf b` is the equivalence of smooth duals `B̌ ≃ B̌'` given by the inverse
  transpose (`smoothContragredientEquiv b.symm`).
- `productCoefficientTensorMap h hU A` is the product comparison
  `I(A) ⊗ I(Ǎ) → I^{G×G}(A ⊠ Ǎ)` (`normalizedProductInductionTensorEquiv`) as a linear map into
  `productInducedCoefficientObject`. It is surjective (`coefficientTensorMap_surjective`). On a
  pure tensor the coefficient transport `productInducedCoefficientTransport` is the tensor of the
  two pointwise transports (`transport_coefficientTensorMap`). These three declarations are for a
  locally compact, second countable nonarchimedean group `G` with a semidirect decomposition
  `P = M ⋉ U`, closed `U` and compact quotient `P \ G`, as required by
  `normalizedProductInductionTensorEquiv`.
- `productInducedCompactEquiv_transport_selfTwist` is a square on the fixed compact pictures.
  Let `e₁ : X ≃ A₀ ⊗ χ₁`, `e₂ : X' ≃ A₀ ⊗ χ₂`, `c : X ≃ X'` and a self-twist
  `a : A₀ ≃ A₀ ⊗ τ` satisfy `e₂ ∘ c = a ∘ e₁` on vectors. Then the restriction to `K × K` of
  `e₂ c Y` is the self-twist operator `productCompactSelfTwistEquiv` of `a` applied to the
  restriction of `e₁ Y`. The group here is an arbitrary locally compact nonarchimedean group with
  a semidirect decomposition `P = M ⋉ U`, closed `P` and `U`, a compact open `K` with `G = PK`, a
  continuous Levi projection and continuous positive characters.

## The two factors

`cFactor` is the composite of six maps: the translation `λ(s)` (`factorTranslation`), the source
Levi-twist comparison, the standard integral `J_{P_α|s·P}` (`factorIntertwiner`), the inverse
target comparison, the restriction to `M'` (`factorRestriction`) and the comparison
`restrictedConjugateEquiv`. `cFactor_apply` states this decomposition (it holds by definition).
Each of these maps commutes with pointwise transport:

- `factorTranslation_natural`, `normalizedInductionLeviEquiv_transport_source`,
  `normalizedInductionLeviEquiv_symm_transport_target` and `factorRestriction_natural` hold
  pointwise;
- `factorIntertwiner_natural` is the naturality of the full-domain standard integral,
  `StandardIntertwining.fullSourceIntertwiner_natural`, for convergent inducing data.

`lowerPullbackEquiv`, `conjugateRepEquiv` and `restrictedRepEquiv` are the equivalences of the
pullbacks with the linear map of `b`. `cFactor_lowerPullback_natural` combines the six steps: the factor of `B'`
after transport by `b` is the transport by `b`, read on `s·M`, of the factor of `B`.
`factorConverges_of_equiv` and `cConverges_of_equiv` show that convergence of one integral, resp.
of both, is invariant under `b` (`StandardIntertwining.domain_eq_top_of_equiv`).
`cDualFactor_apply` and `cDualFactor_natural` give the same for the dual factor, with
`contragredientEquivOf`.

## The c-map

`cMap_apply` unfolds `cMap` as `γ(G|M')⁻¹` times the product comparison of the tensor of the two
factors (by definition). `cMap_tmul` evaluates it on a pure tensor `v ⊗ v̌` as
`γ(G|M')⁻¹ (v_s ⊗ v̌_s)`. `cMap_natural` is the naturality of the c-map. If both integrals
converge for `B` and `B'`, then the c-map of `B'` after the coefficient transport by `b` equals
the coefficient transport by `b`, read on `s·M`, of the c-map of `B`. The proof checks the
identity on pure tensors by `cMap_tmul`, `cFactor_lowerPullback_natural` and `cDualFactor_natural`
(`TensorProduct.ext'`). It then extends to all coefficients by surjectivity of the product
comparison.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), registered as `waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`), V.1, printed pp.288–289. There
`c_{P'|P}(s, ω)(v ⊗ v̌) = γ(G|M')⁻¹ [J_{P_s|s·P}(sω) λ(s) v ⊗ J_{P̃_s|s·P}(sω̌) λ(s) v̌]`.
Waldspurger states that this operator is rational in `ω` and regular at the `G`-regular points of
the unitary orbit `O` (by Proposition IV.2.2). It need not be regular at the other points of `O`.
The Library's c-map is this formula at a single representation, built from the standard integrals
on their full convergence domain. `cMap_natural` is therefore a pointwise identity, assumed only
where both standard integrals converge for `B` and for `B'`. It expresses the dependence of the
operator on the class of the inducing representation as transport through the equivalence `b`.
The results of this module are derived from the definitions and the naturality of the standard
integrals; Waldspurger does not state them separately.
