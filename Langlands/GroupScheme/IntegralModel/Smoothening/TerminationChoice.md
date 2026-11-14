# Termination of the smoothening sequence: adapted generators of the augmentation ideal

Author: Worker 348. Internal helper module for Kaletha–Prasad, Theorem A.6.2. It chooses the
generators used in the defect count of `TerminationCore`. The argument is internal to this project.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

Setting: `R` is a local ring with maximal ideal `𝔪` and residue field `k`. `C` is an `R`-algebra
with an `R`-point `ε`, augmentation ideal `I = augIdeal ε` and cotangent module
`T = Cot ε = I / I²`. `J` is an ideal of `C`. When a uniformizer is involved,
`𝔪 = Ideal.span {ϖ}`, and `ptIdeal ε ϖ = ε⁻¹(ϖ R)` is defined in `TerminationKrull`.

## The data

`GoodChoice ε ϖ J` is a structure with the following fields:
- natural numbers `c` and `t`;
- elements `z : Fin c → C` with `z k ∈ J ∩ I` (`z_mem_J`, `z_mem_I`);
- elements `x : Fin t → C` with `x j ∈ I` (`x_mem_I`);
- `R`-linear forms `l : Fin c → (T →ₗ[R] k)` dual to the differentials of the `z k`:
  `l m (d z_k) = δ_{km}` (`hl`);
- `hgen`: `I ≤ (z) + (x) + ptIdeal ε ϖ · I`;
- `hxind`: if `∑ a_j x_j ∈ J + I²` with `a_j ∈ R`, then all `a_j ∈ 𝔪`.

## Lemmas

- `rho ε : T → k ⊗[R] T` is `t ↦ 1 ⊗ t`. `rho_eq_zero_iff`: its kernel is `𝔪 T`.
  `exists_rho_dif`: every element of `k ⊗ T` is `rho (d i)` for some `i ∈ I`.
- `imageJ ε J` is the `k`-subspace `{rho (d j) : j ∈ J ∩ I}` of `k ⊗ T` (`mem_imageJ`).
- `dif_mul_of_mem`: `d(c y) = ε(c) d y` for `y ∈ I`.
- `cot_finite`: for Noetherian `C`, `T` is a finitely generated `R`-module, spanned by the
  differentials of generators of `I`.
- `mem_of_rho_dif_eq_zero`: if `y ∈ I` and `rho (d y) = 0`, then `y ∈ ptIdeal ε ϖ · I`. The kernel
  of `I → k ⊗ T` is `𝔪 I + I²`, and `I² ⊆ ptIdeal ε ϖ · I`.
- `rho_dif_algebraMap_mul`: `rho (d (r y)) = residue r • rho (d y)`.
- `exists_goodChoice` (**existence**): for Noetherian `C` and `𝔪 = (ϖ)`, a `GoodChoice ε ϖ J`
  exists.

  Proof: `k ⊗ T` is finite-dimensional. Choose a complement `W'` of `imageJ ε J` and bases of both
  parts. Take `z k ∈ J ∩ I` lifting the basis of `imageJ`, and `x j ∈ I` lifting the basis of `W'`.
  The forms `l m` are the coordinate functions of the combined basis, composed with `rho`.
  - For `hgen`, subtract from `i ∈ I` the combination of the `z k` and `x j` with lifted
    coordinates. The remainder has zero image in `k ⊗ T`, so it lies in `ptIdeal ε ϖ · I`.
  - For `hxind`, suppose `∑ a_j x_j = j₀ + q` with `j₀ ∈ J` and `q ∈ I²`. Then
    `rho (d j₀) = ∑ residue(a_j) · (basis of W')` lies in `imageJ ∩ W' = 0`. So all residues
    vanish.
