# A three-term complex of finite projective modules computing the obstruction cone

Module `Langlands.Cohomology.ModuleComplex.ObstructionCone.Model`, namespace of the same name.
This is an internal helper for `Langlands.Cohomology.ModuleComplex.ObstructionCone.openStatement`.

## Data

The data are:
- a complex `(K, dK)` of `A`-modules indexed by `ℕ`;
- `A`-modules `F`, `Q`, `G₀`, `G₁` and maps `δ : Q → F`, `p : G₀ → Q`, `g : G₁ → G₀`;
- cochains `θ ∈ K 1 ⊗ F` and `z₀ ∈ K 2 ⊗ G₀`.

`Module.Dual A G` is `G →ₗ[A] A`.

## Definitions

- `contract t M : (N →ₗ M) → X ⊗ M` sends `D` to `D.lTensor X t` (`contract_apply`).
- `a : F^∨ × K 0 → G₀^∨ × K 1`, `a (f, β) = (−(f ∘ δ ∘ p), rid (f.lTensor θ) + dK 0 β)`
  (`a_apply`). Here `rid` is `TensorProduct.rid : K 1 ⊗ A ≃ K 1`.
- `b : G₀^∨ × K 1 → G₁^∨ × K 2`, `b (f, γ) = (f ∘ g, rid (f.lTensor z₀) + dK 1 γ)`
  (`b_apply`).
- For an `A`-module `M`:
  - `aM : Hom(F, M) × K 0 ⊗ M → Hom(G₀, M) × K 1 ⊗ M`, `(D, β) ↦ (−(D ∘ δ ∘ p), D_* θ + dK β)`;
  - `bM : Hom(G₀, M) × K 1 ⊗ M → Hom(G₁, M) × K 2 ⊗ M`, `(w, γ) ↦ (w ∘ g, w_* z₀ + dK γ)`.
- `termEquiv M G X : (G^∨ × X) ⊗ M ≃ Hom(G, M) × (X ⊗ M)`, for `G` finite projective. It is
  `TensorProduct.prodLeft` followed by Mathlib's `dualTensorHomEquiv` on the first factor
  (`termEquiv_tmul`).

## Results

- `rid_contract_tmul`: `rid (f.lTensor t) ⊗ m = (dualTensorHom (f ⊗ m)).lTensor t`, by
  induction on `t`.
- `ladder_a`, `ladder_b`: `termEquiv ∘ (a ⊗ M) = aM ∘ termEquiv`, and likewise for `b`,
  when `F`, `G₀`, `G₁` are finite projective. Both are checked on pure tensors.
- `exact_rTensor_iff`: `a ⊗ M`, `b ⊗ M` are exact at the middle if and only if `aM`, `bM`
  are. This is Mathlib's `Function.Exact.iff_of_ladder_linearEquiv`.
- `b_comp_a`: `b ∘ a = 0` under these hypotheses:
  - `p ∘ g = 0`;
  - `p.lTensor (K 2) z₀ = zh`;
  - `dK θ = δ_* zh`;
  - `dK 1 ∘ dK 0 = 0`.
- `exact_aM_bM_iff`: assume `p` is surjective, `Function.Exact g p` (so `G₁ → G₀ → Q → 0`
  is a presentation), `p_* z₀ = zh`, `dK θ = δ_* zh` and `dK 1 ∘ dK 0 = 0`. Then middle
  exactness of `aM`, `bM` is equivalent to `HOneVanishes K dK δ θ zh M`.
  - Forward: apply exactness to `(ψ ∘ p, c)`, then cancel `p` using surjectivity.
  - Backward: a `w : G₀ → M` with `w ∘ g = 0` factors as `ψ ∘ p`, via
    `Submodule.liftQ` and `Function.Exact.linearEquivOfSurjective`. The vanishing then
    supplies a preimage under `aM`.

## Provenance

Internal. This is the explicit finite form of the cone of Artin's Axioms, Lemmas 98.23.3
and 98.23.4 (Tag 07YM, 07YN) of The Stacks Project, with `E` replaced by the cochain-level
data `θ`, `z₀` and a free presentation of `Q`.
