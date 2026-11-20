# Exactness consequences for a single element generating a normalized field

Internal helper module for the proof of BK93 (2.2.8) (`RefinementProof`). `E` is a
nonarchimedean local field, `V` a finite-dimensional `E`-space, `𝓛` a lattice chain over `𝒪[E]`,
and `c ∈ End_E(V)`. Assume the generated algebra `E[c]` is a field (`hfield`) whose units
normalize `𝓛` (`hnorm`). This is the situation of a pure stratum (`Stratum.IsPure`). The
results specialize the Library's T2 (`adjointExactness`, BK93 (1.4.4), (1.4.7), (1.4.10),
pp. 36–38) and T1 (`tameCorestriction`, BK93 (1.3.3)) to the field `E[c]` with generator `c`.

- `elementGenerator` and `adjoin_elementGenerator`: `c`, as an element of the field `E[c]`,
  generates it. `subfieldEmbedding_elementGenerator`: its action on `V` is `c`.
- `commute_of_elementAlgebra_eq_bot`: a scalar `c` commutes with everything.
  `not_exists_algebraMap_elementGenerator`: if `E[c] ≠ E`, then `c` is not a scalar.
- `exists_isGreatest_criticalIndexSet`: if `c` is not a scalar, the critical index set has a
  greatest element, and it equals `criticalExponent 𝓛 c` (T2).
- `exists_commute_sub_mem` (**V1**): suppose `k₀(c) ≤ k` and `cγ - γc ∈ 𝔓^{m+k}`. Then
  `γ ≡ γ₁ (mod 𝔓^m)` for some `γ₁` commuting with `c`. Proof: by middle exactness of T2's third
  sequence, applied to a tame corestriction from T1, there is `x ∈ 𝔔^m 𝔑_k` with
  `cx - xc = cγ - γc`. Take `γ₁ = γ - x`. Then `γ₁` commutes with `c`, and
  `γ - γ₁ = x ∈ 𝔔^m 𝔑_k ⊆ 𝔓^m`. A scalar `c` is treated directly with `γ₁ = γ`.
- `mem_criticalIndexSet_of_mem` (**V3**): if `c` is not a scalar and `c ∈ 𝔓^r`, then `r` is a
  critical index of `c`. Otherwise `𝔄 ⊆ 𝔑_r(c) ⊆ 𝔅 + 𝔓^1`. Then the Library's
  `adjointMap_eq_zero_of_order_le` (with `one_mem_centralizerLattice_mul_neg`) would force `c`
  to be central, hence a scalar.
