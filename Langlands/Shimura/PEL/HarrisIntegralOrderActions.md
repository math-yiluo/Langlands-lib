# Finite equations and rational extension for the actual Harris order

This internal construction specializes `FiniteFreeRingHom`,
`IntegralOrderActions` and `IntegralOrderExtension` to the actual order from
`HarrisIntegralOrder`. It reuses that published order and its full-lattice and
finiteness theorems, together with the published actual integral and rational
endomorphism pullbacks. It introduces no new geometric input or original-source
translation.

The number fields `E,K`, rational algebra `A`, central simple unitary data `D`
and Harris signature charts `C` have exactly the hypotheses displayed in
`HarrisIntegralOrder`, with independent universe levels. The order
`O = D.harrisHodgePELIntegralOrder C` is the same order preserved by the
positive auxiliary left involution. No alternative order or involution is
selected. The scheme universe is independent of these arithmetic universes.

Since the existing order is a full integer lattice in a rational vector space,
Mathlib's lattice freeness theorem makes it free over the integers. Its existing
finite-generation theorem then supplies the finite basis
`harrisHodgePELIntegralBasis`, indexed by `Fin (Module.finrank ℤ O)`.
Callers supply no basis or freeness assumption.

For any actual abelian scheme `B/S`,
`harrisHodgePELIntegralActionEquiv C B` identifies all unital ring maps
`O →+* CategoryTheory.End B` with finite tuples satisfying this basis's unit
and ordered multiplication equations. These are equations in the actual
integral endomorphism ring. The specialization reuses the generic equivalence;
the multiplication convention remains `f*g = g ≫ f`.

Given an actual integral action `a : O →+* CategoryTheory.End B`,
`harrisHodgePELRationalAction` first composes it with the existing ring map
`Rationalization.ofEnd B` and then extends it from the full order to
`A →ₐ[ℚ] AbelianScheme.End0 B`. Its restriction to every `x : O` is exactly
`Rationalization.ofEnd B (a x)`. The uniqueness theorem states that every
rational algebra map with this restriction equals the constructed action.
Thus the construction concerns the same supplied abelian scheme and action.
It does not rely on injectivity of the map into rationalized endomorphisms.

For every scheme map `c : S' ⟶ S`, the integral action is pulled back by the
published `AbelianScheme.baseChangeOrderAction`. The finite-equation equivalence
commutes with this pullback by the generic naturality theorem. Rational
extension also commutes with actual base change: the two rational algebra maps
agree on every order element by `rationalBaseChangeEnd_ofEnd`, so full-order
extensionality proves their equality on `A`. There is no flatness,
Noetherian or connectedness hypothesis.

This result starts with an actual integral action. It does not produce such
an action from a rational action on an abelian scheme, nor construct an
isogenous integral representative. It does not assert injectivity, Rosati
compatibility, a determinant condition, an action parameter scheme, ambient
polarized moduli existence, or normalized CM representability.
