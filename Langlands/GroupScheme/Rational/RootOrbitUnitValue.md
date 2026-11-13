# Galois-equivariant unit values on one actual root orbit

## Setting

`k` and `K` are fields with an algebra `k → K`. No finiteness or Galois hypothesis is used.
`T` is a commutative group scheme over `Spec k`, `G` is a group scheme over `Spec k` with
`[IsAffineHom G.X.hom]`, and `j : T.toGrp ⟶ G`. The actual roots of the base change
`j_K : T_K → G_K` carry the Library's Galois action `rootsGaloisAction` of `K ≃ₐ[k] K`.
For an actual root `β`, `rootOrbitField k K j β` is the fixed field of the stabilizer of
`β`. By `mem_rootOrbitField_iff`, `x` lies in it exactly when every `σ` with `σ • β = β`
fixes `x`.

## Declarations

- `apply_eq_of_smul_eq_of_mem_rootOrbitField`: let `x` lie in `rootOrbitField k K j β`,
  and let `σ • β = τ • β`. Then `σ x = τ x`. Proof: `τ⁻¹ σ` stabilizes `β`, so it fixes
  `x`, and `σ x = τ (τ⁻¹ σ x) = τ x`.
- `exists_rootOrbitValue`: let `c ∈ Kˣ` with `(c : K) ∈ rootOrbitField k K j β`. Then there
  is a function `ψ` from the actual roots of `j_K` to `Kˣ` with three properties:
  1. it is Galois-equivariant: `ψ (σ • γ) = Units.map σ.toMonoidHom (ψ γ)`;
  2. `ψ β = c`;
  3. `ψ γ = 1` for every `γ` outside the Galois orbit of `β`.

  On the orbit, `ψ (τ • β) = τ c` for a chosen `τ`. The previous lemma shows that this does
  not depend on the choice. Off the orbit, `ψ` is `1`, and the orbit's complement is
  Galois-stable. Equivariance on the orbit is `(σ τ) c = σ (τ c)`.

## Provenance

This is an elementary fact about Galois orbits and is internal to the proof of
`QuasiSplitAdjointSimpleRootTransitivityStatement`. The source does not state it separately.
It plays the role of the choice of an element of the factor `k_ã^×` of `T(k)` in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), proof of Lemma 6.4.10 (printed
pp.227–228). Here that choice is recorded as values on the roots: the value at the lift `ã`,
its Galois conjugates at the other lifts, and `1` elsewhere.
