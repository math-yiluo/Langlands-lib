# Normalizer points realizing the same reflection differ by the centralizer

This internal unit proves the uniqueness statement needed for axiom V 2 of a
valuation of the root datum (Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach*, Definition 6.1.2). Two rational normalizer points that realize the
reflection along the same nonzero character, in the sense of the published
`RealizesReflection`, differ by a point centralizing the torus. The hypotheses
are that the torus is split, the relative Weyl group is finite, and its action
on the rational root span is faithful. These hold for maximal split tori of
connected reductive groups, by the published
`IsConnectedReductive.finite_relativeWeylGroup` and
`IsConnectedReductive.relativeWeylAction_injective`.

## Duality on the real cocharacter space

Let `T` be a commutative group scheme over a field.

- `eval_sub_apply` and `eval_zsmul_apply`: the published evaluation `eval T χ`
  is additive and `ℤ`-linear in the character.
- `eq_zero_of_eval_eq_zero`: if `T` is split, a character whose evaluation
  vanishes on the real cocharacter space `V T` is zero. The proof uses
  perfectness of the published integral pairing
  (`IsSplitTorus.isPerfPair_latticePairing`).
- `exists_eval_ne_zero`: consequently a nonzero character takes a nonzero value
  somewhere.
- `eq_zero_of_forall_eval_eq_zero`: if `T` is split, a vector of `V T` on which
  every character vanishes is zero. The proof uses the published real perfect
  pairing `isPerfPair_of_isSplitTorus` and induction on tensors.

## The uniqueness theorem

`smul_pow_eq_add` states the following for a normalizer point `z` that fixes
the kernel of a character `a` pointwise, and a vector `v₀` with
`a(z v₀ - v₀) = 0`: the iterate `z^N v₀` is `v₀ + N (z v₀ - v₀)`.

`RealizesReflection.inv_mul_mem_centralizerPoints` states the following. Let
`T` be split, the relative Weyl group finite, and its action on the root span
injective. Let `a ≠ 0`, and let `n, m` both realize the reflection along `a`.
Then `m⁻¹ n` lies in the published `centralizerPoints`. The proof:

1. `z = m⁻¹ n` fixes the kernel `H` of `a` pointwise and fixes `a` under the
   Weyl action, so `a(z v) = a(v)` for every `v`.
2. Choose `v₀` with `a(v₀) ≠ 0`. Then `z v₀ - v₀ ∈ H`. The class of `z` has
   finite order `N > 0` in the relative Weyl group, so `z^N v₀ = v₀`. By
   `smul_pow_eq_add`, `N (z v₀ - v₀) = 0`, hence `z v₀ = v₀`.
3. Since `V T = H + ℝ v₀`, `z` acts trivially on `V T`. By the duality
   statements and the published contragredience `eval_normalizer_smul`, `z`
   acts trivially on characters.
4. Its relative Weyl class therefore acts trivially on the root span, so it is
   trivial by faithfulness. This means `z` centralizes the torus.

## Provenance and scope

This is an internal deduction from the published normalizer action on the
real cocharacter space (`RealTorusAction`), the published relative Weyl group,
and Mathlib linear algebra. It proves no valuation axiom by itself.
