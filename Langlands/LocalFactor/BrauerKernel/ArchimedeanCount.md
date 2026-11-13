# Counting real places and regrouping products by types

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global argument
(1973, proof of Lemma 4.12) the archimedean factors of the global functional equations cancel
because the relation has dimension zero in each type. This unit provides the two counting facts
used for that cancellation. Both are elementary.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`.

## Results

- `prod_zpow_eq_zpow_sum'`: in a commutative group, `∏_i a ^ f i = a ^ Σ_i f i` for integer
  exponents.
- `prod_types_eq_one` (**regrouping by types**): let `S` be a finite index set, `e : S → ℤ`
  weights, and `t₁, t₂ : S → T` two type assignments with
  `Σ_{g ∈ S} e g ([t₁ g = τ] - [t₂ g = τ]) = 0` for every type `τ`. Then for every map `h` from
  types to a commutative group, `∏_{g ∈ S} (h (t₁ g) · h (t₂ g)⁻¹) ^ e g = 1`. Proof: each factor
  is the product over the finitely many types occurring of `h τ` raised to
  `e g ([t₁ g = τ] - [t₂ g = τ])`; exchange the two products; for each `τ` the exponents sum to
  `0`.
- `realComap`: the real place of `k` below a real place of `M` (Mathlib's `IsReal.comap`).
- `card_realComap_fiber`: if `M / k` is a totally real extension of number fields, each real place
  of `k` has exactly `[M : k]` real places of `M` above it. Proof: Mathlib's
  `unramifedPlacesOver_ncard_add_eq_finrank` (unramified places plus twice the ramified places over
  a place number `[M : k]`); in a totally real field no place is ramified, and the places over
  `r` are exactly the real places whose restriction is `r`.
- `prod_realComap`: consequently, for a totally real `M`, a product over the real places of `M` of
  a function of the place below equals the product over the real places of `k` of its
  `[M : k]`-th powers (`Finset.prod_fiberwise`).
