# Covariance of the c-family under unramified self-twists

This module proves that the c-family on the fixed compact pictures (`cCompactFamily`, module
`RationalWeakExpansionCFamily`) is covariant under self-twists of the inducing representation.
Let `A` be a smooth representation of `M_I(F)` and `τ` an unramified character with a self-twist
`a : A ≃ A ⊗ τ`.

- `cCompactFamily_apply` unfolds `cCompactFamily` at `z` in the joint convergence domain
  `cDomain` (by definition). The compact picture at `z` is extended by `productInducedCompactEquiv`
  and the c-map `cMap` of `A ⊗ z` is applied. The result is transported by `twistPullbackEquiv`
  and restricted to the lower compact picture at the conjugate parameter
  `lowerUnramifiedCharacterConjugation z`.
- `lowerSelfTwist A τ a` is the self-twist `sA ≃ sA ⊗ sτ` of the conjugated representation
  `sA = A ∘ e⁻¹` (`lowerLeviConjugation`) induced by `a`. Its linear map is that of `a`.
- `mul_mem_cDomain_of_selfTwist`: `cDomain` is stable under translation by `τ`. The parameter
  self-twist `parameterSelfTwistEquiv : A ⊗ z ≃ A ⊗ zτ` and `cConverges_of_equiv` (module
  `RationalWeakExpansionCNaturality`) give this.
- `cCompactFamily_selfTwist_aux`: for `z` and `zτ` in `cDomain` and every coefficient `X` of
  `A ⊗ z`, with `Fc` the compact picture of `X`,
  `c(s, A ⊗ zτ)(a · Fc) = (sa) · c(s, A ⊗ z)(Fc)`. Here `a ·` and `(sa) ·` are the self-twist
  operators `productCompactSelfTwistEquiv` of the upper and lower compact pictures.

The proof of `cCompactFamily_selfTwist_aux` is a chain of equalities. The upper self-twist
operator is the restriction of the coefficient transport by `parameterSelfTwistEquiv`
(`productInducedParameterSelfTwist_restriction`). `cMap_natural` moves this transport through the
c-map. The lower restriction of the composite transport is the lower self-twist operator, by the
compact square `productInducedCompactEquiv_transport_selfTwist`, whose hypothesis holds on vectors
by definition of `lowerSelfTwist`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), registered as `waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`), V.1, printed pp.287–289.
There `O_C = {ω₀ ⊗ χ ; χ ∈ X(M)}` is the complex orbit and `O = {ω₀ ⊗ χ ; χ ∈ Im X(M)}` the
unitary orbit, and the operator `c_{P'|P}(s, ω)` is rational in `ω`. The Library's c-family is
indexed by complex parameters `z ∈ X(M)`. If `ω₀ ⊗ τ ≅ ω₀`, then `z` and `zτ` determine the same
class `ω₀ ⊗ z ≅ ω₀ ⊗ zτ` of the complex orbit `O_C`. This class lies in `O` only when `z` is
unitary, and the lemmas here are not restricted to unitary `z`. The fixed compact pictures of the
two fibers are identified through the self-twist. The covariance proved here says that, at
parameters in the joint convergence domain `cDomain`, the Library's c-family on the fixed compact
pictures is compatible with these identifications. It is derived from the definitions and from
`cMap_natural`; Waldspurger does not state it separately.
