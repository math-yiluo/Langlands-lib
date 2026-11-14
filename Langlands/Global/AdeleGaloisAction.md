# Galois action on the adeles of a Galois extension

Helper module for the proof of `GaloisBorelTwistingStatement` (Task 5268).

For a finite extension `L/F` of number fields and `σ ∈ Aut(L/F)`, this module defines the
ring automorphism `σ̃ = ringEquiv F L σ` of `𝔸_L` that corresponds to `σ ⊗ 1` on
`L ⊗_F 𝔸_F` under the canonical isomorphism `numberFieldAdeleTensorEquiv F L`. It proves:

- `ringEquiv_tensor`: `σ̃ (a ⊗ x) = σ(a) ⊗ x`;
- `ringEquiv_algebraMap`, `ringEquiv_adeleInclusion`: `σ̃` restricts to `σ` on the diagonal
  copy of `L` and fixes the image of `𝔸_F`;
- `ringEquiv_eq_sum`, `continuous_ringEquiv`: in a basis of `L/F` the map is a finite sum of
  continuous maps, so it is continuous;
- `idelesMap σ`: the induced continuous automorphism of the ideles `𝔸_L^×`;
- `full_idelesMap`: `σ̃` preserves the normalized idelic absolute value. The proof uses the
  Library criterion `IdeleAbsoluteValue.eq_of_positiveRealIdeles`: the composite
  `|·| ∘ σ̃` is again a continuous character trivial on `L^×` and agreeing with `|·|` on
  the positive real ideles (which `σ̃` fixes), hence equal to `|·|`.

Mathematically this is the standard fact that a Galois automorphism permutes the places of
`L` above each place of `F` and preserves the product of the normalized local absolute values.
