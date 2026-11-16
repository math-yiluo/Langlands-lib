# The inverse of a Cartan block has nonnegative entries

Author: Worker 3657.

Lean module: `Langlands.LinearAlgebra.ArthurCombinatoricsCartanInverse`. It
imports `Langlands.LinearAlgebra.ArthurCombinatorics` (the definitions
`cartanBlock`, `weightCoordinate`) and
`Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate`. It changes no
published file and states no new proposition.

This is a helper for the proof task of
`Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement` (Task 7174). The
task contract lists it as an expected prerequisite: "nonnegativity of the
entries of the inverse of `cartanBlock P Θ`, that is, each weight
`weightCoordinate P Θ i` is a nonnegative combination of the simple roots".

## Setting

`P : RootPairing ι ℝ M N` is a finite (`[Fintype ι]`) crystallographic root
system over `ℝ` with a base `b`, and `Θ ⊆ b.support`. The canonical bilinear
form `P.RootForm` on `M` needs `Fintype ι`; the results about `cartanBlock`
do not depend on the instance, so a consumer with `[Finite ι]` uses
`Fintype.ofFinite`.

## Results

- `pairing_nonpos_of_ne`: `P.pairing i j ≤ 0` for distinct `i, j` in the base
  (Mathlib's `RootPairing.Base.pairingIn_le_zero_of_ne`, cast from `ℤ`).
- `rootForm_root_root`: `B(α_k, α_j) = ⟨α_k, α_j^∨⟩ · B(α_j, α_j) / 2` for
  `B = P.RootForm` (Mathlib's `InvariantForm.two_mul_apply_root_root` for
  `P.toInvariantForm`).
- `rootForm_root_self_pos`: `B(α_j, α_j) > 0` (Mathlib's
  `RootPairing.rootForm_pos_of_ne_zero`).
- `rootForm_simple_nonpos`: `B(α_k, α_j) ≤ 0` for distinct simple roots.
- `nonneg_of_rootForm_nonneg` (the Stieltjes argument): if
  `x = ∑_{k ∈ Θ} w_k α_k` satisfies `B(x, α_j) ≥ 0` for every `j ∈ Θ`, then
  every `w_k ≥ 0`. Write `w = p − z` with `p = max(w, 0)`, `z = max(−w, 0)`,
  and `v(y) = ∑ y_k α_k`. Then `B(v z, v w) = ∑ z_j B(x, α_j) ≥ 0`;
  `B(v z, v p) = ∑_{j,l} z_j p_l B(α_j, α_l) ≤ 0`, because `z_j p_j = 0` and
  `B(α_j, α_l) ≤ 0` for `j ≠ l`. Hence `B(v z, v z) = B(v z, v p) − B(v z, v w)
  ≤ 0`, so `B(v z, v z) = 0`. As `B` is positive definite on the span of the
  roots (`RootPairing.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero`),
  `v z = 0`, and linear independence of the simple roots
  (`b.linearIndepOn_root`) gives `z = 0`.
- `cartanBlock_inv_nonneg`: every entry of `(cartanBlock P Θ)⁻¹` is
  nonnegative. For the row `w` of index `i` of `W = (cartanBlock P Θ)⁻¹`,
  `B(∑_k w_k α_k, α_j) = (W · cartanBlock) i j · B(α_j, α_j)/2 =
  δ_{ij} B(α_j, α_j)/2 ≥ 0` (`rootForm_root_root` and `W · A = 1`,
  `Matrix.nonsing_inv_mul` with the published `isUnit_det_cartanBlock`), and
  the Stieltjes argument applies.
- `weightCoordinate_eq_sum`: `weightCoordinate P Θ i = ∑_k W_{ik} α_k` for
  `i ∈ Θ` (the definition), so with `cartanBlock_inv_nonneg` each weight is a
  nonnegative combination of the simple roots of `Θ`.

## Provenance

Arthur, *A trace formula for reductive groups I* (1978), uses this fact in
the proof of Lemma 6.1 (§6, pp.938–939; registered as
`arthur-1978-trace-formula-reductive-groups-I`, PDF page = printed page −
910) as "the positive chamber is contained in the set of positive linear
combinations of roots". The Lean proof is the standard argument that a
symmetric positive definite matrix with nonpositive off-diagonal entries has
an entrywise nonnegative inverse, applied to the Gram matrix of the simple
roots for the canonical form. It is not taken from Arthur, who quotes the fact
without proof.

## Axioms

Lake-build inspection 4fc5b475 of `cartanBlock_inv_nonneg`: only `propext`,
`Classical.choice` and `Quot.sound`.
