# Proof that closure inflation does not depend on the chosen isomorphism

Author: Worker 272.

This module proves `closureInflationTransportIndependence :
ClosureInflationTransportIndependence.{u,v}`, the published proposition
`Langlands.ClassFieldTheory.Local.ClosureInflationTransportIndependence` of
the module
`Langlands.ClassFieldTheory.Local.ClosureInflationIndependenceStatement`. It
also proves the transport lemmas below, which are public and reusable.

## Transport lemmas

Fields `K`, `L`, `M`, `N` are in independent universes, with `K`-algebra
structures on `L`, `M`, `N`.

- `relativeAutPullback_trans`, `relativeAutPullback_refl`: pulling back a
  Galois automorphism along `e.trans e'` is the pullback along `e'` and then
  along `e`. The pullback along the identity is the identity. Both are checked
  pointwise with `simp`.
- `relativeAutPullback_self`: for an automorphism `τ` of `L`, the pullback of
  `s` is the conjugate `τ⁻¹ * s * τ`.
- `relativeUnitTransport_self`: for an automorphism `τ`, the unit transport is
  the Galois action `(unitsRepresentation K L).ρ τ`. It holds by definition on
  underlying units.
- `relativeCocycleTransport_trans`, `relativeCocycleTransport_refl`: cocycle
  transport is functorial. Proved by `cocycles₂_ext` and the pullback lemmas.
- `relativeH2Equiv_trans`, `relativeH2Equiv_refl`: the same on `H²`. Proved by
  `H2_induction_on` and `relativeH2Equiv_H2π`.
- `relativeH2Equiv_self`: transport along any automorphism `τ` of `L` is the
  identity on `H²(Gal(L/K), L^×)`. This is Serre, *Local Fields*, VII §5,
  Proposition 3, for inner automorphisms. Serre argues by dimension shifting.
  The Lean proof instead gives an explicit primitive. For a cocycle `z`, put
  `b g = z(τ, τ⁻¹ g τ) - z(g, τ)`. The cocycle identity
  `z(gh, j) + z(g, h) = g · z(h, j) + z(g, hj)` is used at the three triples
  `(τ, τ⁻¹sτ, τ⁻¹tτ)`, `(s, τ, τ⁻¹tτ)` and `(s, t, τ)`. The group products are
  normalised with `group`. It follows that
  `τ · z(τ⁻¹sτ, τ⁻¹tτ) - z(s, t) = s · b(t) - b(st) + b(s)`, which is `d₁₂ b`
  at `(s, t)`. The last step is closed by `abel`. Then `H2π_eq_iff` gives
  equality of classes.

## Main theorem

Let `e₁ : L ≃ₐ[K] E₁` and `e₂ : L ≃ₐ[K] E₂` be given, where `E₁` and `E₂` are
finite normal subfields of `AlgebraicClosure K`.

1. `E₁ = E₂`. The composite `ψ = E₁.val ∘ (e₂⁻¹ then e₁) : E₂ →ₐ[K] K̄` has
   field range `E₂` by `AlgHom.fieldRange_of_normal`, because `E₂` is normal.
   Its range is also `E₁`, checked elementwise, because `e₂⁻¹` followed by
   `e₁` is a bijection onto `E₁`.
2. After substituting, `e₂ = e₁.trans (e₁.symm.trans e₂)` by extensionality.
   `relativeH2Equiv_trans` splits the transport. `relativeH2Equiv_self` then
   removes the automorphism `e₁.symm.trans e₂`, which gives the goal.

Only normality and finite dimension are used. Separability is not needed.

Axioms used by the main theorem: `propext`, `Classical.choice`,
`Quot.sound`.
